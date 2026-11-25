package vego

import (
	"go/types"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// hexEdge386 is the longest src whose hex.EncodeToString does not panic on
// a 32-bit target: EncodedLen computes 2 * len(src) as an int, which wraps
// past MaxInt at 1 << 30, and make panics with "len out of range" (F10 of
// the review of S1 of F36).
const hexEdge386 = 1<<30 - 1

// TestEncodedLenEdge evaluates the requires of the shipped entry of
// hex.EncodeToString with the sizes of a 32-bit target at the edge, as
// checkBufferEdges386 does for the buffers. That the edge is right is what
// TestHex386 shows.
func TestEncodedLenEdge(t *testing.T) {
	parallel(t)
	pv, imports := shippedVerifier(t)
	narrow := narrowVerifier(pv)
	pkg, err := imports.Import("encoding/hex")
	if err != nil {
		t.Fatal(err)
	}
	fn := contractOfKey(t, narrow, pkg, "encoding/hex.EncodeToString")
	holds := func(length int) bool {
		check := &sequenceCheck{t: t, pv: narrow, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: lengthTerm(length)}}
		return check.holds(fn.requires)
	}
	if !holds(hexEdge386) || holds(hexEdge386+1) {
		t.Errorf("the requires of hex.EncodeToString on a 32-bit target is %v at %d bytes and %v at %d; the edge is %d", holds(hexEdge386), hexEdge386, holds(hexEdge386+1), hexEdge386+1, hexEdge386)
	}
}

// TestHex386 runs hex.EncodeToString built for 386 on each side of the
// edge of its requires: one byte more panics before it allocates, and the
// edge itself passes the make of the result. At the edge the result and
// its string take 4 GB with the input, which a 32-bit process may not have,
// so there it may also die for want of memory, which is no panic.
func TestHex386(t *testing.T) {
	if os.Getenv("VEGO_386") != "1" {
		t.Skip("set VEGO_386=1 to run hex.EncodeToString at the 32-bit edge of its entry; it needs about 3 GB and systemd-run")
	}
	helper := filepath.Join(t.TempDir(), "hex386")
	build := exec.Command("go", "build", "-o", helper, "./testdata/hex386")
	build.Env = append(os.Environ(), "GOARCH=386")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build the helper: %v\n%s", err, out)
	}
	run := func(n int) string {
		cmd := exec.Command("systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=0", "--",
			"timeout", "300", helper, strconv.Itoa(n))
		out, _ := cmd.CombinedOutput()
		return string(out)
	}
	if out := run(hexEdge386 + 1); !strings.Contains(out, "panic: runtime error: makeslice: len out of range") {
		t.Errorf("hex.EncodeToString of %d bytes on 386 did not panic in make:\n%.2000s", hexEdge386+1, out)
	}
	if out := run(hexEdge386); strings.Contains(out, "panic:") {
		t.Errorf("hex.EncodeToString of %d bytes on 386 panicked:\n%.2000s", hexEdge386, out)
	} else {
		t.Logf("%d bytes: %.200s", hexEdge386, strings.TrimSpace(out))
	}
}
