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
	narrow := *pv
	pass := *pv.pass
	pass.TypesSizes = types.SizesFor("gc", "386")
	narrow.pass = &pass
	helper := filepath.Join(t.TempDir(), "buffers386")
	build := exec.Command("go", "build", "-o", helper, "./testdata/buffers386")
	build.Env = append(os.Environ(), "GOARCH=386")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build the helper: %v\n%s", err, out)
	}
	const maxInt = 1<<31 - 1
	page := func(n int) int { return n / 8192 * 8192 }
	type edge struct {
		name, kind         string
		grow0, written, rd int
		n                  int
		// inside is whether the requires is meant to hold.
		inside bool
	}
	c := 720 << 20
	s := maxInt / 5
	bufferInside := page(2*s - 1)
	n3 := 500000000
	bufferCatch := page(2*(n3+1) - 1)
	builderN := (maxInt - 65536) / 3
	cases := []edge{
		{name: "a Builder of capacity c grown by c+1", kind: "builder", grow0: c, n: c + 1},
		{name: "the worst Builder inside the bound", kind: "builder", grow0: page(builderN - 1), n: builderN, inside: true},
		{name: "a Buffer of capacity c grown by c+1", kind: "buffer", grow0: c, n: c + 1},
		{name: "the worst Buffer inside the bound", kind: "buffer", grow0: bufferInside, written: bufferInside - s + 2, rd: bufferInside - s + 1, n: s - 1, inside: true},
		{name: "a Buffer read down to one byte, grown past the check of ErrTooLarge", kind: "buffer", grow0: bufferCatch, written: bufferCatch - n3 + 1, rd: bufferCatch - n3, n: n3},
	}
	// An append that moves a []byte: the rule of appendFits against the
	// capacity the runtime gives. Past MaxInt the capacity is negative.
	appends := []edge{
		{name: "an append whose capacity rounds past MaxInt", kind: "append", grow0: 879605573, n: 838374793},
		{name: "the longest append inside the rule", kind: "append", grow0: 600000000, n: (maxInt-65536)/2 - 600000000, inside: true},
	}
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
			v := &fnVerifier{pkgVerifier: &narrow}
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
			fn := contractOfKey(t, &narrow, pkg, key)
			check := &sequenceCheck{t: t, pv: &narrow, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: reference(false), fn.params[1]: logic.IntLit(int64(n))},
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
