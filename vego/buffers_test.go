package vego

import (
	"fmt"
	"go/types"
	"math/big"
	"math/rand"
	"reflect"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// This file tests the shipped entries of the methods of strings.Builder
// (and, from the second step of buffers, bytes.Buffer) against the real
// methods. |b| is read as the verifier reads it: by the length formula of
// the type's owns declaration, evaluated over the fields of the real value
// (F4 of the design review), and the harness holds that against Len() and
// what the declaration holds of every value after every call it makes.

// fieldEnv resolves the names of a length formula, or of what an owns
// declaration holds, to the fields of a real struct: an integer field to
// its value and |f| of a slice field to its length.
type fieldEnv struct {
	val reflect.Value
}

func (e fieldEnv) Path(name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	field := e.val.FieldByName(name)
	switch {
	case !field.IsValid():
		return nil, fmt.Errorf("%s has no field %s", e.val.Type(), name)
	case when != logic.Now:
		return nil, fmt.Errorf("%s: a formula of a declaration speaks of one state", name)
	case len(steps) == 1 && steps[0].Len && field.Kind() == reflect.Slice:
		return logic.IntLit(int64(field.Len())), nil
	case len(steps) == 0 && field.CanInt():
		return logic.IntLit(field.Int()), nil
	}
	return nil, fmt.Errorf("%s.%s: the harness reads only integer fields and the lengths of slices", e.val.Type(), name)
}

func (fieldEnv) Relation(name string, paths []logic.Path) (*logic.Term, error) {
	return nil, fmt.Errorf("%s cannot be read of the fields of a value", name)
}

func (fieldEnv) Qualified(path, name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	return nil, fmt.Errorf("%q.%s cannot be read of the fields of a value", path, name)
}

// declaredLength returns |owner| by the length formula of its type's owns
// declaration, for owner a pointer to the struct, and fails unless every
// formula the declaration holds is true of it.
func declaredLength(t *testing.T, pv *pkgVerifier, owner any) int64 {
	t.Helper()
	val := reflect.ValueOf(owner).Elem()
	var decl *ownsDecl
	for _, file := range shippedContracts() {
		if d, ok := file.owns[stateKey(val.Type().PkgPath(), val.Type().Name())]; ok {
			decl = &d
		}
	}
	if decl == nil || decl.length == nil {
		t.Fatalf("%s has no length by the shipped declarations", val.Type())
	}
	env := fieldEnv{val: val}
	term, err := pv.res.IntTerm(decl.length, env)
	if err != nil {
		t.Fatalf("the length %q of %s: %v", decl.lengthText, val.Type(), err)
	}
	eval := &evaluator{bindings: map[string]*big.Int{}, errors: standIn}
	for i, node := range decl.holds {
		held, err := pv.res.Formula(node, env)
		if err != nil {
			t.Fatalf("%q, held by %s: %v", decl.holdsText[i], val.Type(), err)
		}
		if !eval.holds(held) {
			t.Fatalf("%s holds %q, which is false of a value the harness made", val.Type(), decl.holdsText[i])
		}
	}
	return eval.number(term).Int64()
}

// allocated returns the capacity append gives a slice of n bytes made from
// nothing: n rounded up to a size class or a page, as growslice and
// MakeNoZero round what they allocate.
func allocated(n int) int {
	return cap(append([]byte(nil), make([]byte, n)...))
}

// bufferText returns a string of a random length, now and then past the
// 32 KB from which allocations round to pages, and past 256 KB.
func bufferText(rng *rand.Rand) string {
	n := rng.Intn(80)
	switch rng.Intn(20) {
	case 0, 1:
		n = 0
	case 2, 3:
		n = 30000 + rng.Intn(20000)
	case 4:
		// Past 256 KB, where append grows by a quarter and a bound that
		// counts the length once and the rounding fails.
		n = 300000 + rng.Intn(300000)
	}
	return strings.Repeat("x", n)
}

// bufferCall is one call that a harness of a buffer makes: the method by
// the key of its entry, the terms of its parameters after the receiver,
// and how it is made.
type bufferCall struct {
	key   string
	given []*logic.Term
	call  func() []*logic.Term
	// panics is set for a call whose requires is false and that panics,
	// which the harness makes to show that the requires is needed.
	panics bool
}

// checkBufferCall checks one call: the requires with |b| before, the call
// with the growth of what the buffer owns checked, the ensures with |b|
// after, the length against Len(), and, when the call moved the buffer to a
// larger array, that the array is no larger than what each clause of the
// requires that is bounded by MaxAlloc allows. It reports whether the call
// was made.
func checkBufferCall(t *testing.T, pv *pkgVerifier, fn *funcInfo, owner any, length func() int, capacity func() int, arrays *ownerArrays, bc bufferCall) bool {
	t.Helper()
	before := declaredLength(t, pv, owner)
	if before != int64(length()) {
		t.Fatalf("before %s: the declared length is %d and Len is %d", bc.key, before, length())
	}
	var after int64
	c := &sequenceCheck{t: t, pv: pv, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: reference(false)}}
	c.length = func(v *types.Var, when logic.When) *logic.Term {
		if v != fn.params[0] {
			t.Fatalf("the harness knows the length of %s only", fn.params[0].Name())
		}
		if when == logic.Primed {
			return logic.IntLit(after)
		}
		return logic.IntLit(before)
	}
	for i, param := range fn.params[1:] {
		c.given[param] = bc.given[i]
	}
	if !c.holds(fn.requires) {
		if bc.panics {
			defer func() {
				if recover() == nil {
					t.Fatalf("%s with its requires false did not panic", bc.key)
				}
			}()
			bc.call()
		}
		return false
	}
	if bc.panics {
		t.Fatalf("the requires of %s holds of a call that panics", bc.key)
	}
	oldCap := capacity()
	arrays.checkGrowth(t, owner, bc.key, func() { c.results = bc.call() })
	after = declaredLength(t, pv, owner)
	if after != int64(length()) {
		t.Fatalf("after %s: the declared length is %d and Len is %d", bc.key, after, length())
	}
	c.ensure(bc.key)
	if newCap := capacity(); newCap > oldCap {
		// A clause L <= MaxAlloc of the requires claims that what the call
		// allocates, rounded, is at most L; the array it moved to is.
		for _, cl := range fn.requires {
			for _, node := range cl.node.Conjuncts() {
				if node.Kind != logic.NCompare || len(node.Ops) != 1 || node.Ops[0] != "<=" || node.Kids[1].Kind != logic.NIdent || node.Kids[1].Name != "MaxAlloc" {
					continue
				}
				bound, err := pv.res.IntTerm(node.Kids[0], c.env())
				if err != nil {
					t.Fatalf("%s %q: %v", cl.kind, cl.text, err)
				}
				eval := &evaluator{bindings: map[string]*big.Int{}, errors: standIn}
				if allowed := eval.number(bound); big.NewInt(int64(newCap)).Cmp(allowed) > 0 {
					t.Fatalf("%s grew the buffer from %d bytes, %d of them written, to %d, more than the %s that its requires %q bounds", bc.key, oldCap, before, newCap, allowed, cl.text)
				}
			}
		}
	}
	return true
}

// checkBuilderEntries runs the entries of the methods of strings.Builder.
// Each round makes a Builder and calls its methods at random, each only when
// its requires holds; Grow is also called with a negative count, which
// must fail the requires and panic. The method under test must be called
// with its requires true often enough to matter.
func checkBuilderEntries(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	names := []string{"Write", "WriteString", "WriteByte", "WriteRune", "Grow", "Len", "String", "Reset"}
	contracts := map[string]*funcInfo{}
	for _, name := range names {
		contracts["(*strings.Builder)."+name] = contractOfKey(t, pv, pkg, "(*strings.Builder)."+name)
	}
	if contracts[key] == nil {
		t.Fatalf("no harness calls %s; add it to checkBuilderEntries", key)
	}
	rng := rand.New(rand.NewSource(1))
	arrays := &ownerArrays{}
	checked := 0
	for range 100 {
		b := new(strings.Builder)
		for range 1 + rng.Intn(16) {
			var bc bufferCall
			// Half the calls are of the method under test, the others
			// bring the Builder to the states it is called in.
			name := names[rng.Intn(len(names))]
			if rng.Intn(2) == 0 {
				name = strings.TrimPrefix(key, "(*strings.Builder).")
			}
			switch name {
			case "Write":
				p := []byte(bufferText(rng))
				if rng.Intn(4) == 0 {
					// Just past the free capacity, where the new array is
					// largest for what is written.
					p = make([]byte, b.Cap()-b.Len()+1)
				}
				bc = bufferCall{given: []*logic.Term{lengthTerm(len(p))}, call: func() []*logic.Term {
					n, err := b.Write(p)
					return []*logic.Term{logic.IntLit(int64(n)), errorTerm(err)}
				}}
			case "WriteString":
				s := bufferText(rng)
				bc = bufferCall{given: []*logic.Term{lengthTerm(len(s))}, call: func() []*logic.Term {
					n, err := b.WriteString(s)
					return []*logic.Term{logic.IntLit(int64(n)), errorTerm(err)}
				}}
			case "WriteByte":
				c := byte(rng.Intn(256))
				bc = bufferCall{given: []*logic.Term{logic.IntLit(int64(c))}, call: func() []*logic.Term {
					return []*logic.Term{errorTerm(b.WriteByte(c))}
				}}
			case "WriteRune":
				r := anyRune(rng)
				bc = bufferCall{given: []*logic.Term{logic.IntLit(int64(r))}, call: func() []*logic.Term {
					n, err := b.WriteRune(r)
					return []*logic.Term{logic.IntLit(int64(n)), errorTerm(err)}
				}}
			case "Grow":
				n := rng.Intn(100)
				switch rng.Intn(6) {
				case 0:
					n = -1 - rng.Intn(10)
				case 1:
					n = 40000 + rng.Intn(40000)
				case 2:
					// Just past the free capacity, where Grow allocates the
					// most for what it is asked.
					n = b.Cap() - b.Len() + 1
				}
				bc = bufferCall{given: []*logic.Term{logic.IntLit(int64(n))}, call: func() []*logic.Term {
					b.Grow(n)
					return nil
				}, panics: n < 0}
			case "Len":
				bc = bufferCall{call: func() []*logic.Term { return []*logic.Term{logic.IntLit(int64(b.Len()))} }}
			case "String":
				bc = bufferCall{call: func() []*logic.Term { return []*logic.Term{lengthTerm(len(b.String()))} }}
			case "Reset":
				bc = bufferCall{call: func() []*logic.Term {
					b.Reset()
					return nil
				}}
			}
			bc.key = "(*strings.Builder)." + name
			if checkBufferCall(t, pv, contracts[bc.key], b, b.Len, b.Cap, arrays, bc) && bc.key == key {
				checked++
			}
		}
	}
	if checked < 50 {
		t.Fatalf("%s was called with its requires true %d times; the harness should reach it more often", key, checked)
	}
}

// anyRune returns a code point below 128, one above it, a surrogate, a
// value past the last code point, or a negative value, which WriteRune
// writes as U+FFFD.
func anyRune(rng *rand.Rand) rune {
	switch rng.Intn(5) {
	case 0:
		return rune(rng.Intn(128))
	case 1:
		return rune(128 + rng.Intn(0x10FFFF-128))
	case 2:
		return rune(0xD800 + rng.Intn(0x800))
	case 3:
		return rune(0x110000 + rng.Intn(1000))
	}
	return -1 - rune(rng.Intn(1000))
}

// TestBuilderCopyPanics shows what the sentence of "What a proof assumes"
// about copies of a strings.Builder rests on: a Builder that is not zero,
// copied by value, panics at its next write, while a copy of a zero one
// does not. Verified code never copies one (the copy rule); code that is
// not verified is assumed not to, as the documentation of Builder asks.
func TestBuilderCopyPanics(t *testing.T) {
	parallel(t)
	var zero strings.Builder
	copied := zero
	copied.WriteByte('a')
	var used strings.Builder
	used.WriteByte('a')
	again := used
	defer func() {
		if r := recover(); r == nil || !strings.Contains(fmt.Sprint(r), "copied by value") {
			t.Fatalf("a write to a copy of a Builder that is not zero gave %v, not the panic of copyCheck", r)
		}
	}()
	again.WriteByte('b')
}
