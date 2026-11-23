package vego

import (
	"fmt"
	"go/types"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// mediaTypeFactor reads the factor of the requires of the shipped entry of
// mime.ParseMediaType, factor * (|v| + 1) + 65536 <= MaxAlloc, which bounds
// what a call allocates in all.
func mediaTypeFactor(t *testing.T) int64 {
	t.Helper()
	var entry *trustEntry
	for _, file := range shippedContracts() {
		if e, ok := file.entries["mime.ParseMediaType"]; ok {
			entry = e
		}
	}
	if entry == nil || len(entry.requires) != 1 {
		t.Fatal("the test reads one requires of a shipped entry of mime.ParseMediaType")
	}
	m := regexp.MustCompile(`^(\d+) \* \(\|v\| \+ 1\) \+ 65536 <= MaxAlloc$`).FindStringSubmatch(entry.requires[0].text)
	if m == nil {
		t.Fatalf("the requires of mime.ParseMediaType is %q, and the test reads factor * (|v| + 1) + 65536 <= MaxAlloc", entry.requires[0].text)
	}
	factor, err := strconv.ParseInt(m[1], 10, 64)
	if err != nil {
		t.Fatal(err)
	}
	return factor
}

// buildMediaType builds testdata/mediatype with the environment given and
// returns the path of the helper and the names of its shapes.
func buildMediaType(t *testing.T, env ...string) (string, []string) {
	t.Helper()
	helper := filepath.Join(t.TempDir(), "mediatype")
	build := exec.Command("go", "build", "-o", helper, "./testdata/mediatype")
	build.Env = append(os.Environ(), env...)
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build the helper: %v\n%s", err, out)
	}
	out, err := exec.Command(helper, "shapes").Output()
	if err != nil {
		t.Fatalf("list the shapes: %v", err)
	}
	return helper, strings.Fields(string(out))
}

// mediaTypeRuns reads what the helper printed: the length of each value and
// the bytes its call allocated.
func mediaTypeRuns(t *testing.T, out []byte) (lengths, allocated []int64) {
	t.Helper()
	for line := range strings.Lines(string(out)) {
		var length, alloc int64
		if _, err := fmt.Sscanf(line, "len %d alloc %d", &length, &alloc); err != nil {
			t.Fatalf("read %q: %v", line, err)
		}
		lengths, allocated = append(lengths, length), append(allocated, alloc)
	}
	if len(lengths) == 0 {
		t.Fatalf("the helper printed nothing")
	}
	return lengths, allocated
}

// TestMediaTypeBound measures what mime.ParseMediaType allocates in all on
// the shapes of value that cost the most for each byte, at lengths from 5
// bytes to 256 KB, against the requires of its shipped entry. The
// shapes are in testdata/mediatype: a media type of invalid bytes, which
// lowercasing makes three each; parameters with distinct names, upper case;
// RFC 2231 continuations of one value; an encoded value; and parameters with
// a star and distinct names, each of which makes a map of its own, in every
// form a star takes.
func TestMediaTypeBound(t *testing.T) {
	factor := mediaTypeFactor(t)
	helper, shapes := buildMediaType(t)
	var lengths []string
	for l := 5.0; l < 1<<18; l *= 1.15 {
		lengths = append(lengths, strconv.Itoa(int(l)))
	}
	for _, shape := range shapes {
		out, err := exec.Command(helper, append([]string{shape}, lengths...)...).CombinedOutput()
		if err != nil {
			t.Fatalf("%s: %v\n%s", shape, err, out)
		}
		got, allocated := mediaTypeRuns(t, out)
		worst := 0.0
		for i, length := range got {
			if bound := factor*(length+1) + 65536; allocated[i] > bound {
				t.Errorf("%s: ParseMediaType of %d bytes allocated %d bytes, more than the entry's bound of %d", shape, length, allocated[i], bound)
			}
			if allocated[i] > 65536 {
				worst = max(worst, float64(allocated[i]-65536)/float64(length+1))
			}
		}
		t.Logf("%s: at most %.1f bytes for each byte of the value beyond 65536, against %d", shape, worst, factor)
	}
}

// TestMIME386 runs mime.ParseMediaType on a 32-bit target on the
// longest value of each shape that the requires of its entry admits there,
// each in a 4G scope of its own, and fails unless the call returns having
// allocated no more than the bound. The requires is evaluated with the sizes
// of GOARCH=386 to hold at that length and not one byte past it.
func TestMIME386(t *testing.T) {
	if os.Getenv("VEGO_386") != "1" {
		t.Skip("set VEGO_386=1 to run mime.ParseMediaType at the 32-bit edge of its entry; it needs about 1 GB and systemd-run")
	}
	pv, imports := shippedVerifier(t)
	narrow := narrowVerifier(pv)
	factor := mediaTypeFactor(t)
	pkg, err := imports.Import("mime")
	if err != nil {
		t.Fatal(err)
	}
	fn := contractOfKey(t, narrow, pkg, "mime.ParseMediaType")
	holds := func(length int64) bool {
		check := &sequenceCheck{t: t, pv: narrow, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: lengthTerm(int(length))}}
		return check.holds(fn.requires)
	}
	maxAlloc := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 32), big.NewInt(1))
	edge := new(big.Int).Sub(maxAlloc, big.NewInt(65536))
	edge.Div(edge, big.NewInt(factor)).Sub(edge, big.NewInt(1))
	n := edge.Int64()
	if !holds(n) || holds(n+1) {
		t.Fatalf("the requires of mime.ParseMediaType on a 32-bit target is %v at %d bytes and %v at %d, and the edge is computed to lie between", holds(n), n, holds(n+1), n+1)
	}
	helper, shapes := buildMediaType(t, "GOARCH=386")
	for _, shape := range shapes {
		run := exec.Command("systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=0", "--",
			"timeout", "300", helper, shape, strconv.FormatInt(n, 10))
		out, err := run.CombinedOutput()
		if err != nil {
			shown := string(out)
			if len(shown) > 2000 {
				shown = shown[:2000]
			}
			t.Errorf("%s: a value of at most %d bytes, inside the requires, did not return: %v\n%s", shape, n, err, shown)
			continue
		}
		got, allocated := mediaTypeRuns(t, out)
		if !holds(got[0]) {
			t.Fatalf("%s: the helper built %d bytes, outside the requires", shape, got[0])
		}
		if bound := factor*(got[0]+1) + 65536; allocated[0] > bound {
			t.Errorf("%s: ParseMediaType of %d bytes allocated %d bytes, more than the entry's bound of %d", shape, got[0], allocated[0], bound)
		}
		t.Logf("%s: %d bytes of value, %d allocated, %.1f for each byte", shape, got[0], allocated[0], float64(allocated[0])/float64(got[0]+1))
	}
}
