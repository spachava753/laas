package vego

import (
	"fmt"
	"go/types"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// TestBuffers386 holds the MaxInt clauses of the entries of Grow against
// the real methods on a 32-bit target, where they are reached (F3 of the
// design review): it builds testdata/buffers386 for GOARCH=386, runs each
// case in a scope limited to 4 GB, and fails if the requires holds of a
// call that panicked, or if a case meant to lie at the edge of the bound
// does not lie on the side it was built for. It needs a few GB of memory
// and systemd-run, so it runs only with VEGO_386=1.
//
// The cases: a Builder of capacity c grown by c+1 and a Buffer the same,
// which panic, and which a clause with a smaller factor would allow; the
// worst Builder and the worst Buffer inside the bound, which return; and a
// Buffer read down to one byte whose growth panics at the check of
// ErrTooLarge, which the Buffer's clause with 4 in place of 5 allows. The
// rule an append must prove (appendFits) is held the same way: an append
// whose capacity, rounded, passes MaxInt, where growslice gives a negative
// capacity and no panic, and the longest append inside the rule.
func TestBuffers386(t *testing.T) {
	if os.Getenv("VEGO_386") != "1" {
		t.Skip("set VEGO_386=1 to run the 32-bit cases of the buffer entries; they need about 3 GB and systemd-run")
	}
	alone(t)
	pv, imports := shippedVerifier(t)
	narrow := narrowVerifier(pv)
	helper := filepath.Join(t.TempDir(), "buffers386")
	build := exec.Command("go", "build", "-o", helper, "./testdata/buffers386")
	build.Env = append(os.Environ(), "GOARCH=386")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build the helper: %v\n%s", err, out)
	}
	cases, appends := edges386()
	for _, e := range appends {
		t.Run(e.name, func(t *testing.T) {
			run := exec.Command("systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=0", "--",
				helper, e.kind, strconv.Itoa(e.grow0), "0", "0", strconv.Itoa(e.n))
			out, err := run.CombinedOutput()
			if err != nil {
				t.Fatalf("the helper failed: %v\n%s", err, out)
			}
			var length, capacity, n int
			var panicked bool
			var message string
			if _, err := fmt.Sscanf(string(out), "len %d cap %d n %d panicked %t %q", &length, &capacity, &n, &panicked, &message); err != nil {
				t.Fatalf("read %q: %v", out, err)
			}
			v := &fnVerifier{pkgVerifier: narrow}
			holds, known := groundHolds(v.appendFits(logic.IntLit(int64(length+n)), types.Typ[types.Byte]))
			t.Logf("append of %d to %d bytes: capacity %d, the rule holds %v, panicked %v %s", n, length, capacity, holds, panicked, message)
			switch {
			case !known:
				t.Fatalf("the rule of appendFits is not ground for a ground length")
			case holds && (panicked || capacity < length+n):
				t.Errorf("the rule of appendFits holds of an append that panicked or made a capacity of %d", capacity)
			case holds != e.inside:
				t.Errorf("the case was built to lie %s the rule, and it is %v", map[bool]string{true: "inside", false: "outside"}[e.inside], holds)
			case !e.inside && capacity >= length+n && !panicked:
				t.Errorf("the case outside the rule made a good slice, so it shows nothing of the rule")
			}
		})
	}
	for _, e := range cases {
		t.Run(e.name, func(t *testing.T) {
			key := map[string]string{"builder": "(*strings.Builder).Grow", "buffer": "(*bytes.Buffer).Grow"}[e.kind]
			shipped := false
			for _, file := range shippedContracts() {
				shipped = shipped || file.entries[key] != nil
			}
			if !shipped {
				t.Skipf("%s has no shipped entry", key)
			}
			run := exec.Command("systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=0", "--",
				helper, e.kind, strconv.Itoa(e.grow0), strconv.Itoa(e.written), strconv.Itoa(e.rd), strconv.Itoa(e.n))
			out, err := run.CombinedOutput()
			if err != nil {
				t.Fatalf("the helper failed: %v\n%s", err, out)
			}
			var length, capacity, n int
			var panicked bool
			var message string
			if _, err := fmt.Sscanf(string(out), "len %d cap %d n %d panicked %t %q", &length, &capacity, &n, &panicked, &message); err != nil {
				t.Fatalf("read %q: %v", out, err)
			}
			pkg, err := imports.Import(map[string]string{"builder": "strings", "buffer": "bytes"}[e.kind])
			if err != nil {
				t.Fatal(err)
			}
			fn := contractOfKey(t, narrow, pkg, key)
			check := &sequenceCheck{t: t, pv: narrow, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: reference(false), fn.params[1]: logic.IntLit(int64(n))},
				length: func(*types.Var, logic.When) *logic.Term { return logic.IntLit(int64(length)) }}
			holds := check.holds(fn.requires)
			t.Logf("Len %d, Cap %d, Grow(%d): requires %v, panicked %v %s", length, capacity, n, holds, panicked, message)
			switch {
			case holds && panicked:
				t.Errorf("the requires of %s holds and the call panicked: %s", key, message)
			case holds != e.inside:
				t.Errorf("the case was built to lie %s the bound, and the requires is %v", map[bool]string{true: "inside", false: "outside"}[e.inside], holds)
			case !e.inside && !panicked:
				t.Errorf("the case outside the bound did not panic, so it shows nothing of the clause")
			case strings.Contains(message, "out of memory"):
				t.Errorf("the helper ran out of memory, which says nothing of the clause")
			}
		})
	}
}

// edge386 is a case of TestBuffers386: how the helper brings a buffer to
// its state, what Grow is then asked, or for an append the length of the
// full slice and how much of it is appended; and whether the requires, or
// the rule of appendFits, is meant to hold.
type edge386 struct {
	name, kind         string
	grow0, written, rd int
	n                  int
	inside             bool
}

// edges386 returns the cases of TestBuffers386, which TestBufferEdges386
// also evaluates without running them.
func edges386() (cases, appends []edge386) {
	const maxInt = 1<<31 - 1
	page := func(n int) int { return n / 8192 * 8192 }
	c := 720 << 20
	s := maxInt / 5
	bufferInside := page(2*s - 1)
	n3 := 500000000
	bufferCatch := page(2*(n3+1) - 1)
	builderN := (maxInt - 65536) / 3
	cases = []edge386{
		{name: "a Builder of capacity c grown by c+1", kind: "builder", grow0: c, n: c + 1},
		{name: "the worst Builder inside the bound", kind: "builder", grow0: page(builderN - 1), n: builderN, inside: true},
		{name: "a Buffer of capacity c grown by c+1", kind: "buffer", grow0: c, n: c + 1},
		{name: "the worst Buffer inside the bound", kind: "buffer", grow0: bufferInside, written: bufferInside - s + 2, rd: bufferInside - s + 1, n: s - 1, inside: true},
		{name: "a Buffer read down to one byte, grown past the check of ErrTooLarge", kind: "buffer", grow0: bufferCatch, written: bufferCatch - n3 + 1, rd: bufferCatch - n3, n: n3},
	}
	// An append that moves a []byte: the rule of appendFits against the
	// capacity the runtime gives. Past MaxInt the capacity is negative.
	appends = []edge386{
		{name: "an append whose capacity rounds past MaxInt", kind: "append", grow0: 879605573, n: 838374793},
		{name: "the longest append inside the rule", kind: "append", grow0: 600000000, n: (maxInt-65536)/2 - 600000000, inside: true},
	}
	return cases, appends
}

// narrowVerifier returns a copy of a verifier of the shipped entries for a
// 32-bit target, whose MaxInt and MaxAlloc are those of GOARCH=386.
func narrowVerifier(pv *pkgVerifier) *pkgVerifier {
	narrow := *pv
	pass := *pv.pass
	pass.TypesSizes = types.SizesFor("gc", "386")
	narrow.pass = &pass
	return &narrow
}

// checkBufferEdges386 evaluates, with the sizes of a 32-bit target, the
// requires of Grow of both buffers and the rule of appendFits at the cases
// TestBuffers386 holds against the runtime, and the requires of
// WriteString of a Builder at the cases of an append, which is what it is
// (F7 of the review of step 1). It needs neither the helper nor memory, so
// it runs by default, in TestShippedContracts, and a clause or a rule made
// weaker than the runtime needs on such a target fails here; that the
// numbers are right is what the run with VEGO_386=1 shows.
func checkBufferEdges386(t *testing.T, pv *pkgVerifier, imports types.Importer) {
	narrow := narrowVerifier(pv)
	cases, appends := edges386()
	requires := func(key string, length, n int) bool {
		path := key[strings.Index(key, "*")+1 : strings.Index(key, ".")]
		pkg, err := imports.Import(path)
		if err != nil {
			t.Fatal(err)
		}
		fn := contractOfKey(t, narrow, pkg, key)
		check := &sequenceCheck{t: t, pv: narrow, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: reference(false)},
			length: func(*types.Var, logic.When) *logic.Term { return logic.IntLit(int64(length)) }}
		if types.Identical(fn.params[1].Type(), types.Typ[types.Int]) {
			check.given[fn.params[1]] = logic.IntLit(int64(n))
		} else {
			check.given[fn.params[1]] = lengthTerm(n)
		}
		return check.holds(fn.requires)
	}
	for _, e := range cases {
		key := map[string]string{"builder": "(*strings.Builder).Grow", "buffer": "(*bytes.Buffer).Grow"}[e.kind]
		if holds := requires(key, e.written-e.rd, e.n); holds != e.inside {
			t.Errorf("%s: the requires of %s is %v on a 32-bit target, and the case was built to lie %s it", e.name, key, holds, map[bool]string{true: "inside", false: "outside"}[e.inside])
		}
	}
	v := &fnVerifier{pkgVerifier: narrow}
	for _, e := range appends {
		if holds, _ := groundHolds(v.appendFits(logic.IntLit(int64(e.grow0+e.n)), types.Typ[types.Byte])); holds != e.inside {
			t.Errorf("%s: the rule of appendFits is %v on a 32-bit target, and the case was built to lie %s it", e.name, holds, map[bool]string{true: "inside", false: "outside"}[e.inside])
		}
		if holds := requires("(*strings.Builder).WriteString", e.grow0, e.n); holds != e.inside {
			t.Errorf("%s: the requires of (*strings.Builder).WriteString, an append, is %v on a 32-bit target, and the case was built to lie %s it", e.name, holds, map[bool]string{true: "inside", false: "outside"}[e.inside])
		}
	}
}
