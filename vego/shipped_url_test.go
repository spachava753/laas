package vego

import (
	"go/types"
	"math/big"
	"math/rand"
	"net/url"
	"strings"
	"testing"
	"unsafe"

	"github.com/spachava753/laas/vego/internal/logic"
)

// checkQueryEntry runs the entry of (*net/url.URL).Query: the requires
// read with |u.RawQuery| from the real URL, the call, and the ensures, with
// fresh(result) told from the real memory.
func checkQueryEntry(t *testing.T, pv *pkgVerifier, fn *funcInfo) {
	rng := rand.New(rand.NewSource(28))
	calls := 0
	for range 400 {
		u := &url.URL{Path: "/x", RawQuery: randomQuery(rng)}
		c := &sequenceCheck{t: t, pv: pv, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: reference(false)}}
		c.path = func(name string, steps []logic.Step, when logic.When) *logic.Term {
			if name == fn.params[0].Name() && len(steps) == 2 && steps[0].Field == "RawQuery" && steps[1].Len {
				return logic.IntLit(int64(len(u.RawQuery)))
			}
			return nil
		}
		if !c.holds(fn.requires) {
			continue
		}
		calls++
		before := snapshot(u)
		m := u.Query()
		if fingerprint(u) != before[0].(snapped).print {
			t.Fatalf("Query changed the URL it was called on")
		}
		c.results = []*logic.Term{reference(m == nil)}
		c.fresh = map[*types.Var]bool{fn.results[0]: m != nil && !newWalk(nil, true, u).objects[*(*uintptr)(unsafe.Pointer(&m))]}
		c.ensure("Query")
	}
	if calls == 0 {
		t.Fatalf("no call of Query was made")
	}
}

// TestQueryBound measures the largest allocation of Query on the worst
// shape of a query, "a&a&...&a", whose one key gets a slice of a string per
// parameter, against the requires of the entry, with the limit of
// GODEBUG=urlmaxqueryparams lifted as code that is not verified may; and it
// evaluates the requires at the edge of a 32-bit target, where a string
// takes 8 bytes and the largest slice is at most twice the parameters.
func TestQueryBound(t *testing.T) {
	alone(t)
	t.Setenv("GODEBUG", "urlmaxqueryparams=0")
	pv, imports := shippedVerifier(t)
	pkg, err := imports.Import("net/url")
	if err != nil {
		t.Fatal(err)
	}
	fn := contractOfKey(t, pv, pkg, "(*net/url.URL).Query")
	// clause evaluates the left side of the requires bounded by MaxAlloc
	// for a query of n bytes.
	clause := func(n int64) int64 {
		c := &sequenceCheck{t: t, pv: pv, fn: fn, given: map[*types.Var]*logic.Term{fn.params[0]: reference(false)}}
		c.path = func(name string, steps []logic.Step, when logic.When) *logic.Term {
			if len(steps) == 2 && steps[0].Field == "RawQuery" && steps[1].Len {
				return logic.IntLit(n)
			}
			return nil
		}
		for _, cl := range fn.requires {
			for _, node := range cl.node.Conjuncts() {
				if node.Kind == logic.NCompare && len(node.Ops) == 1 && node.Ops[0] == "<=" && node.Kids[1].Kind == logic.NIdent && node.Kids[1].Name == "MaxAlloc" {
					bound, err := pv.res.IntTerm(node.Kids[0], c.env())
					if err != nil {
						t.Fatal(err)
					}
					eval := &evaluator{bindings: map[string]*big.Int{}, errors: standIn}
					return eval.number(bound).Int64()
				}
			}
		}
		t.Fatalf("the requires of Query has no clause bounded by MaxAlloc")
		return 0
	}
	for _, params := range []int{1, 10, 1000, 100000, 1000000, 3000000} {
		q := strings.Repeat("a&", params-1) + "a"
		v := (&url.URL{RawQuery: q}).Query()
		if len(v["a"]) != params {
			t.Fatalf("Query of %d parameters gave %d values; the limit of urlmaxqueryparams is not lifted", params, len(v["a"]))
		}
		if largest := 16 * int64(cap(v["a"])); largest > clause(int64(len(q))) {
			t.Errorf("Query of %d bytes allocated a slice of %d bytes, more than the %d its requires allows", len(q), largest, clause(int64(len(q))))
		}
	}
	// The longest query the requires admits on a 32-bit target, where a
	// string takes 8 bytes and the slice of one key at most twice as many
	// as there are parameters, (n + 1) / 2: it must be one that can be
	// allocated, and an int must hold its size.
	maxAlloc386 := int64(1)<<32 - 1
	n := int64(0)
	for step := int64(1) << 40; step > 0; step >>= 1 {
		if clause(n+step) <= maxAlloc386 {
			n += step
		}
	}
	if worst := 2 * ((n + 1) / 2) * 8; worst > maxAlloc386 || worst > 1<<31-1 {
		t.Errorf("at the edge, %d bytes on a 32-bit target, the slice of one key may take %d bytes, which cannot be allocated", n, worst)
	}
}
