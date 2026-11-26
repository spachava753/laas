package vego

import (
	"fmt"
	"math/big"
	"slices"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// platform is what the arithmetic of the runtime depends on: the width of an
// int and of a uintptr, and the most one allocation can be.
type platform struct {
	name     string
	bits     uint
	maxAlloc int64
}

func (t platform) maxInt() int64 { return 1<<(t.bits-1) - 1 }

// wrap gives what an int computation yields on the platform.
func (t platform) wrap(x int64) int64 {
	if t.bits == 64 {
		return x
	}
	return int64(int32(x))
}

// roundup is roundupsize for a large allocation, which goes up to a whole
// number of pages of 8192 bytes, and for a small one, which stays within a
// size class of at most 32768 bytes.
func roundup(size int64) int64 {
	if size <= 32768 {
		return 32768
	}
	return (size + 8191) / 8192 * 8192
}

// nextslicecap is the runtime's, in the platform's int arithmetic.
func (t platform) nextslicecap(newLen, oldCap int64) int64 {
	newcap := oldCap
	doublecap := t.wrap(newcap + newcap)
	if newLen > doublecap {
		return newLen
	}
	if oldCap < 256 {
		return doublecap
	}
	for {
		newcap = t.wrap(newcap + (newcap+768)>>2)
		if uint64(newcap)&(1<<t.bits-1) >= uint64(newLen) {
			break
		}
	}
	if newcap <= 0 {
		return newLen
	}
	return newcap
}

// grow is growslice: it reports the capacity of the new array and whether
// the runtime panics, for a newLen computed in the platform's ints, or makes
// a slice whose capacity, the rounded size divided by the element's, is
// not an int (F15 of the review of step 3: for elements of one byte the
// runtime sets newcap = int(capmem), which on 386 is negative for a rounded
// size past MaxInt, and what is sliced of it next panics), as appendFits
// counts it.
func (t platform) grow(newLen, oldCap, size int64) (int64, bool) {
	if newLen < 0 {
		return 0, true
	}
	newcap := t.nextslicecap(newLen, oldCap)
	mem := new(big.Int).Mul(big.NewInt(newcap), big.NewInt(size))
	if !mem.IsInt64() || roundup(mem.Int64()) > t.maxAlloc {
		return 0, true
	}
	capacity := roundup(mem.Int64()) / size
	if capacity > t.maxInt() {
		return 0, true
	}
	return capacity, false
}

// makeNoZero is bytealg.MakeNoZero, which strings.Builder's Grow calls: it
// panics for a length past maxAlloc, and rounds the length up to what the
// allocator gives, of which unsafe.Slice panics past MaxInt.
func (t platform) makeNoZero(n int64) bool {
	return n < 0 || n > t.maxAlloc || roundup(n) > t.maxInt()
}

// make is makeslice of bytes: whether it panics.
func (t platform) make(n int64) bool {
	return n < 0 || n > t.maxAlloc
}

// readFileFits replays os.ReadFile of a file that reports a size of at most
// n bytes and yields at most n: the make of the size and one byte, and every
// slices.Grow by 512 when the slice is full, or, for a size of 0, when less
// than 512 bytes are left.
func readFileFits(tg platform, n int64) string {
	for _, statSize := range []int64{0, 1, n / 2, n - 600, n - 300, n - 1, n} {
		size := statSize
		if size > tg.maxInt() {
			size = 0
		}
		size = tg.wrap(size + 1)
		size = max(size, 512)
		if tg.make(size) {
			return fmt.Sprintf("a stat size of %d makes %d bytes", statSize, size)
		}
		length, capacity := int64(0), size
		for length < n {
			length = min(capacity, n)
			left := capacity - length
			if left != 0 && !(statSize == 0 && left < 512) {
				continue
			}
			if length == n && left != 0 {
				break
			}
			newLen := tg.wrap(length + 512)
			grown, panics := tg.grow(newLen, capacity, 1)
			if panics {
				return fmt.Sprintf("a stat size of %d: growing %d bytes by 512 panics", statSize, length)
			}
			capacity = grown
		}
	}
	return ""
}

// readAllFits replays io.ReadAll of a reader that yields n bytes: chunks of
// 512, 256, and half again more each, moved on when less than a sixteenth
// is left, and one slice of the total at the end.
func readAllFits(tg platform, n int64) string {
	total, capacity, next := int64(0), int64(512), int64(256)
	for {
		length := min(capacity, n-total)
		if total+length >= n {
			break
		}
		total = tg.wrap(total + length)
		if total < 0 {
			return "the total read passes MaxInt"
		}
		if _, panics := tg.grow(next, 0, 1); panics {
			return fmt.Sprintf("a chunk of %d bytes panics", next)
		}
		capacity = next
		next = tg.wrap(next + next/2)
		if next < 0 {
			return "the size of the next chunk passes MaxInt"
		}
	}
	if tg.wrap(n) != n {
		return "the total read passes MaxInt"
	}
	if _, panics := tg.grow(n, 0, 1); panics {
		return fmt.Sprintf("the final slice of %d bytes panics", n)
	}
	return ""
}

// readStringFits replays ReadString of n bytes through a Reader of the
// smallest buffer: the headers of collectFragments, and a Builder grown to
// the total.
func readStringFits(tg platform, n int64) string {
	if why := fragmentsFit(tg, n); why != "" {
		return why
	}
	if tg.wrap(n) != n || tg.makeNoZero(n) {
		return fmt.Sprintf("the Builder grown to %d bytes panics", n)
	}
	return ""
}

// readBytesFits replays ReadBytes of n bytes: the headers of
// collectFragments, and a slice of the total made by make, which does not
// round.
func readBytesFits(tg platform, n int64) string {
	if why := fragmentsFit(tg, n); why != "" {
		return why
	}
	if tg.wrap(n) != n || tg.make(n) {
		return fmt.Sprintf("the slice of %d bytes panics", n)
	}
	return ""
}

// fragmentsFit replays collectFragments over n bytes through a Reader of
// the smallest buffer, 16 bytes: a slice header of 24 bytes for each full
// buffer, appended one at a time.
func fragmentsFit(tg platform, n int64) string {
	count := n / 16
	length, capacity := int64(0), int64(0)
	for length < count {
		if length == capacity {
			newLen := tg.wrap(length + 1)
			grown, panics := tg.grow(newLen, capacity, 24)
			if panics {
				return fmt.Sprintf("the headers of %d full buffers panic", length+1)
			}
			capacity = grown
		}
		// Every append up to the capacity is free; jump to it.
		length = min(capacity, count)
	}
	return ""
}

// inputsEdges are the functions whose entries name Inputs, with the replay
// of what each allocates.
var inputsEdges = map[string]func(platform, int64) string{
	"os.ReadFile":                readFileFits,
	"io.ReadAll":                 readAllFits,
	"(*bufio.Reader).ReadString": readStringFits,
	"(*bufio.Reader).ReadBytes":  readBytesFits,
}

// TestInputsEdges holds the constants of the requires that name Inputs
// (F14 of the review of step 3 of F39): on a 32-bit and a 64-bit platform, at
// the largest Inputs that the entry's requires admit, the replay of what
// the function allocates neither passes MaxInt nor MaxAlloc; and each
// constant of a clause that names Inputs, made one step weaker (a factor
// one less, an addend dropped, a clause dropped), admits an Inputs at which
// the replay panics on one of the targets.
func TestInputsEdges(t *testing.T) {
	parallel(t)
	targets := []platform{{"386", 32, 1<<32 - 1}, {"amd64", 64, 1 << 48}}
	var files []*trustFile
	files = append(files, shippedContracts()...)
	for key, fits := range inputsEdges {
		var clauses []*logic.Node
		for _, file := range files {
			if entry := file.entries[key]; entry != nil {
				for _, f := range entry.requires {
					if inputsWord.MatchString(f.text) {
						clauses = append(clauses, f.node)
					}
				}
			}
		}
		if len(clauses) == 0 {
			t.Errorf("%s has no clause that names Inputs", key)
			continue
		}
		for _, tg := range targets {
			n := largestInputs(t, clauses, tg)
			if why := fits(tg, n); why != "" {
				t.Errorf("%s on %s at Inputs = %d, the largest its requires admit: %s", key, tg.name, n, why)
			}
		}
		// Each constant one step weaker must fail on some platform.
		for i, clause := range clauses {
			for j, weaker := range weakenings(clause) {
				changed := slices.Clone(clauses)
				if weaker == nil {
					changed = slices.Delete(changed, i, i+1)
				} else {
					changed[i] = weaker
				}
				failed := false
				for _, tg := range targets {
					if n := largestInputs(t, changed, tg); fits(tg, n) != "" {
						failed = true
					}
				}
				if !failed && weaker != nil {
					t.Errorf("%s: weakening %d of %q still fits on both targets", key, j, strings.TrimSpace(fmt.Sprint(clause)))
				}
			}
		}
	}
}

// largestInputs is the largest Inputs below 2^62 at which every clause
// holds on the platform.
func largestInputs(t *testing.T, clauses []*logic.Node, tg platform) int64 {
	holds := func(n int64) bool {
		env := map[string]*big.Int{"Inputs": big.NewInt(n), "MaxInt": big.NewInt(tg.maxInt()), "MaxAlloc": big.NewInt(tg.maxAlloc)}
		for _, c := range clauses {
			if ok, err := groundFormula(c, env); err != nil {
				t.Fatalf("%v", err)
			} else if !ok {
				return false
			}
		}
		return true
	}
	lo, hi := int64(0), int64(1)<<62
	if !holds(lo) {
		t.Fatalf("no Inputs is admitted")
	}
	for lo < hi {
		mid := lo + (hi-lo+1)/2
		if holds(mid) {
			lo = mid
		} else {
			hi = mid - 1
		}
	}
	return lo
}

// weakenings returns the clause with each of its constants one step weaker:
// a factor of Inputs one less, an addend 0; and nil for the clause dropped.
func weakenings(clause *logic.Node) []*logic.Node {
	var out []*logic.Node
	var visit func(n *logic.Node, rebuild func(*logic.Node) *logic.Node)
	visit = func(n *logic.Node, rebuild func(*logic.Node) *logic.Node) {
		if n.Kind == logic.NBinary && (n.Op == "*" || n.Op == "+") {
			for k, kid := range n.Kids {
				if kid.Kind == logic.NInt {
					lit := *kid
					if n.Op == "*" {
						lit.Big = new(big.Int).Sub(kid.Big, big.NewInt(1))
					} else {
						lit.Big = big.NewInt(0)
					}
					copied := *n
					copied.Kids = slices.Clone(n.Kids)
					copied.Kids[k] = &lit
					out = append(out, rebuild(&copied))
				}
			}
		}
		for k, kid := range n.Kids {
			visit(kid, func(replaced *logic.Node) *logic.Node {
				copied := *n
				copied.Kids = slices.Clone(n.Kids)
				copied.Kids[k] = replaced
				return rebuild(&copied)
			})
		}
	}
	visit(clause, func(n *logic.Node) *logic.Node { return n })
	return append(out, nil)
}

// groundFormula evaluates a clause of numbers, names of env, +, -, *, and
// chains of comparisons.
func groundFormula(n *logic.Node, env map[string]*big.Int) (bool, error) {
	var value func(n *logic.Node) (*big.Int, error)
	value = func(n *logic.Node) (*big.Int, error) {
		switch n.Kind {
		case logic.NInt:
			return n.Big, nil
		case logic.NIdent:
			if v, ok := env[n.Name]; ok {
				return v, nil
			}
		case logic.NBinary:
			a, err := value(n.Kids[0])
			if err != nil {
				return nil, err
			}
			b, err := value(n.Kids[1])
			if err != nil {
				return nil, err
			}
			switch n.Op {
			case "+":
				return new(big.Int).Add(a, b), nil
			case "-":
				return new(big.Int).Sub(a, b), nil
			case "*":
				return new(big.Int).Mul(a, b), nil
			}
		}
		return nil, fmt.Errorf("cannot evaluate %v", n)
	}
	if n.Kind != logic.NCompare {
		return false, fmt.Errorf("not a comparison: %v", n)
	}
	for i, op := range n.Ops {
		a, err := value(n.Kids[i])
		if err != nil {
			return false, err
		}
		b, err := value(n.Kids[i+1])
		if err != nil {
			return false, err
		}
		c := a.Cmp(b)
		if !map[string]bool{"<": c < 0, "<=": c <= 0, "=": c == 0, ">": c > 0, ">=": c >= 0}[op] {
			return false, nil
		}
	}
	return true, nil
}
