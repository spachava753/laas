package vego

import (
	"go/types"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// TestEncoding386 holds the factors of the bound vego proves at a call of
// json.Marshal and json.MarshalIndent (3 and a page within MaxAlloc, 5
// within MaxInt, and what a map's entries allocate) against the real
// functions on a 32-bit target, where they are reached: it builds
// testdata/json386 for GOARCH=386 in each build of encoding/json, and runs
// each case at the largest value inside the bound in a scope limited to
// 4 GB. Each must return. It needs a few GB of memory and systemd-run, so
// it runs only with VEGO_386=1, and with VEGO_GO126=1 it covers Go 1.26.6
// too.
func TestEncoding386(t *testing.T) {
	if os.Getenv("VEGO_386") != "1" {
		t.Skip("set VEGO_386=1 to run the 32-bit cases of the entries of encoding/json; they need about 3 GB and systemd-run")
	}
	alone(t)
	sizes := types.SizesFor("gc", "386")
	maxAlloc := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 32), big.NewInt(1))
	str := types.Typ[types.String]
	cases := []struct {
		name     string
		t        types.Type
		indented bool
	}{
		{"string", str, false},
		{"bytes", types.NewSlice(types.Typ[types.Byte]), false},
		{"map", types.NewMap(types.Typ[types.Int32], types.Typ[types.Bool]), false},
		{"indent", types.NewSlice(str), true},
	}
	for _, b := range jsonBuilds() {
		helper := filepath.Join(t.TempDir(), "json386")
		build := exec.Command("go", "build", "-o", helper, "./testdata/json386")
		build.Env = append(append(os.Environ(), "GOARCH=386"), b.env...)
		if out, err := build.CombinedOutput(); err != nil {
			t.Fatalf("build the helper for %s: %v\n%s", b.name, err, out)
		}
		for _, c := range cases {
			why, walk := jsonPlainReason(nil, sizes, c.t, "v")
			if why != "" {
				t.Fatal(why)
			}
			// The largest n at which what is built fits, every length at
			// most n, through the same function a call is proved by;
			// MarshalIndent with no prefix and an indent of two.
			fits := func(n *big.Int) bool {
				total := walk.total(func(l jsonLength) *big.Int {
					switch l.text {
					case "|prefix|":
						return big.NewInt(0)
					case "|indent|":
						return big.NewInt(2)
					}
					return n
				}, c.indented)
				return jsonFits(total, maxAlloc, sizes)
			}
			lo, hi := big.NewInt(0), new(big.Int).Lsh(big.NewInt(1), 32)
			for new(big.Int).Sub(hi, lo).Cmp(big.NewInt(1)) > 0 {
				mid := new(big.Int).Rsh(new(big.Int).Add(lo, hi), 1)
				if fits(mid) {
					lo = mid
				} else {
					hi = mid
				}
			}
			run := exec.Command("systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=0", "--",
				"timeout", "300", helper, c.name, lo.String())
			out, err := run.CombinedOutput()
			if err != nil {
				shown := string(out)
				if len(shown) > 2000 {
					shown = shown[:2000]
				}
				t.Errorf("%s: %s at %s, inside the bound, did not return: %v\n%s", b.name, c.name, lo, err, shown)
				continue
			}
			t.Logf("%s: %s at %s built %s bytes", b.name, c.name, lo, strings.TrimSpace(string(out)))
		}
	}
}

// TestEdgesOfEncodingBound holds the bound vego proves a call of json.Marshal
// against, with the sizes of GOARCH=386, at values TestEncoding386 ran on
// the real encoders: each value that returned in every build fits, and a
// value whose encoding failed in one build does not. A string of 100
// million NULs, 600 million bytes encoded, ran out of address space in v1
// (Go 1.27.3 with GOEXPERIMENT=nojsonv2, 3.7 GB in use), where 90 million
// returned; the clause 5 * total <= MaxInt is what refuses it, so a factor
// of 3 or less fails here. The page and the factor of 3 within MaxAlloc
// cannot be shown this way: on 386 the MaxInt clause binds first, and a
// 64-bit edge is past this machine; they are the factors of a growing
// bytes.Buffer derived for its entries (F26).
func TestEdgesOfEncodingBound(t *testing.T) {
	parallel(t)
	sizes := types.SizesFor("gc", "386")
	maxAlloc := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 32), big.NewInt(1))
	str := types.Typ[types.String]
	for _, c := range []struct {
		t    types.Type
		n    int64
		fits bool
	}{
		{str, 71582787, true},
		{types.NewSlice(types.Typ[types.Byte]), 214748362, true},
		{types.NewMap(types.Typ[types.Int32], types.Typ[types.Bool]), 6607641, true},
		{str, 100000000, false},
	} {
		_, walk := jsonPlainReason(nil, sizes, c.t, "v")
		total := walk.total(func(jsonLength) *big.Int { return big.NewInt(c.n) }, false)
		if got := jsonFits(total, maxAlloc, sizes); got != c.fits {
			t.Errorf("%s at %d: the bound says it fits %v, and the run says %v", c.t, c.n, got, c.fits)
		}
	}
}
