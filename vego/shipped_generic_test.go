package vego

import (
	"fmt"
	"go/types"
	"math/big"
	"math/rand"
	"reflect"
	"slices"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The shipped entries of generic functions are tested at each of several
// type arguments: the entry's contract of that instantiation is built as a
// call builds it, and checked against the real function instantiated
// there. An instantiation at which the entry cannot be used is tested too,
// by the defect its contract must have.

// Types of the harness, with the same shapes as the types made for them in
// the package of the shipped verifier (see harnessTypes).
type (
	harnessPoint struct{ X, Y int }
	harnessIDs   []int
	harnessEmpty struct{}
)

// harnessTypes are the types of the type arguments of the harness.
type harnessTypes struct {
	point, ids, empty types.Type
}

func newHarnessTypes(pkg *types.Package) *harnessTypes {
	named := func(name string, underlying types.Type) types.Type {
		return types.NewNamed(types.NewTypeName(0, pkg, name, nil), underlying, nil)
	}
	intT := types.Typ[types.Int]
	field := func(name string) *types.Var { return types.NewField(0, pkg, name, intT, false) }
	return &harnessTypes{
		point: named("harnessPoint", types.NewStruct([]*types.Var{field("X"), field("Y")}, nil)),
		ids:   named("harnessIDs", types.NewSlice(intT)),
		empty: named("harnessEmpty", types.NewStruct(nil, nil)),
	}
}

// genericCase is one instantiation of a generic function with a shipped
// entry: the type arguments, and either the harness that calls the real
// function at them, or a part of the defect the contract must have there.
type genericCase struct {
	targs   func(h *harnessTypes) []types.Type
	harness func(rng *rand.Rand) sample
	refused string
}

func sliceOf(elem func(h *harnessTypes) types.Type) func(h *harnessTypes) []types.Type {
	return func(h *harnessTypes) []types.Type { return []types.Type{types.NewSlice(elem(h)), elem(h)} }
}

func basic(kind types.BasicKind) func(*harnessTypes) types.Type {
	return func(*harnessTypes) types.Type { return types.Typ[kind] }
}

func pointType(h *harnessTypes) types.Type   { return h.point }
func pointerType(h *harnessTypes) types.Type { return types.NewPointer(h.point) }
func emptyType(h *harnessTypes) types.Type   { return h.empty }
func idsArgs(h *harnessTypes) []types.Type   { return []types.Type{h.ids, types.Typ[types.Int]} }

// pointPool is the memory the pointers of the harness point to, so that two
// elements are often the same pointer.
var pointPool = []*harnessPoint{{1, 2}, {1, 2}, {3, 4}}

// Elements of each type, from few values so that elements are often equal.
func smallInt(rng *rand.Rand) int         { return rng.Intn(4) - 1 }
func smallInt64(rng *rand.Rand) int64     { return int64(rng.Intn(4)) << 40 }
func smallByte(rng *rand.Rand) byte       { return byte(rng.Intn(3)) * 120 }
func smallString(rng *rand.Rand) string   { return []string{"", "a", "b", "ab"}[rng.Intn(4)] }
func smallPoint(rng *rand.Rand) harnessPoint {
	return harnessPoint{rng.Intn(2), rng.Intn(2)}
}
func smallPointer(rng *rand.Rand) *harnessPoint {
	return pointPool[rng.Intn(len(pointPool))]
}
func smallFloat(rng *rand.Rand) float64   { return randomFloat(rng) }
func anyEmpty(*rand.Rand) harnessEmpty    { return harnessEmpty{} }

// randomSliceOf returns a slice of up to six elements, at times nil, at
// times empty and not nil, and at times with room beyond its length.
func randomSliceOf[E any](rng *rand.Rand, elem func(*rand.Rand) E) []E {
	switch rng.Intn(8) {
	case 0:
		return nil
	case 1:
		return make([]E, 0, rng.Intn(3))
	}
	n := rng.Intn(7)
	s := make([]E, n, n+rng.Intn(4))
	for i := range s {
		s[i] = elem(rng)
	}
	return s
}


// sliceCall calls a function of one slice, which it may write.
func sliceCall[S ~[]E, E any](gen func(*rand.Rand) S, call func(S) []any) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s := gen(rng)
		before := snapshot(s)
		results := call(s)
		return sample{before: before, after: []any{s}, results: results}
	}
}

// sliceValueCall calls a function of a slice and a value.
func sliceValueCall[S ~[]E, E, V any](gen func(*rand.Rand) S, val func(*rand.Rand) V, call func(S, V) []any) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, v := gen(rng), val(rng)
		before := snapshot(s, v)
		results := call(s, v)
		return sample{before: before, after: []any{s, v}, results: results}
	}
}

// sliceFuncCall calls a function of a slice and a predicate on its
// elements, which answers at random and records what it is given.
func sliceFuncCall[S ~[]E, E any](gen func(*rand.Rand) S, name string, call func(S, func(E) bool) []any) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, calls := gen(rng), map[string][][]any{}
		f := recorder(rng, calls, name, randomBool[E])
		before := snapshot(s)
		results := call(s, f)
		return sample{before: []any{before[0], f}, after: []any{s, f}, results: results, calls: calls}
	}
}

func gen[E any](elem func(*rand.Rand) E) func(*rand.Rand) []E {
	return func(rng *rand.Rand) []E { return randomSliceOf(rng, elem) }
}

func genIDs(rng *rand.Rand) harnessIDs { return harnessIDs(randomSliceOf(rng, smallInt)) }

// sortedGen is gen, sorted three times in four.
func sortedGen[E interface{ ~int | ~int64 | ~uint8 }](elem func(*rand.Rand) E) func(*rand.Rand) []E {
	return func(rng *rand.Rand) []E {
		s := randomSliceOf(rng, elem)
		if rng.Intn(4) > 0 {
			slices.Sort(s)
		}
		return s
	}
}

// one wraps a single result.
func one[R any](r R) []any { return []any{r} }

// growCall calls Grow with a room that is often more than the slice has.
func growCall[S ~[]E, E any](gen func(*rand.Rand) S) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, n := gen(rng), rng.Intn(6)-1
		before := snapshot(s)
		if n < 0 {
			return sample{before: []any{before[0], n}, after: []any{s, n}}
		}
		return sample{before: []any{before[0], n}, after: []any{s, n}, results: []any{slices.Grow(s, n)}}
	}
}

// deleteCall calls Delete with bounds that are often valid.
func deleteCall[S ~[]E, E any](gen func(*rand.Rand) S) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s := gen(rng)
		i, j := rng.Intn(len(s)+2)-1, rng.Intn(len(s)+2)
		if rng.Intn(3) > 0 {
			i = rng.Intn(len(s) + 1)
			j = i + rng.Intn(len(s)-i+1)
		}
		before := snapshot(s)
		if i < 0 || i > j || j > len(s) {
			return sample{before: []any{before[0], i, j}, after: []any{s, i, j}}
		}
		return sample{before: []any{before[0], i, j}, after: []any{s, i, j}, results: []any{slices.Delete(s, i, j)}}
	}
}

// insertCall calls Insert with an index that is often valid and values
// passed as a slice of their own.
func insertCall[S ~[]E, E any](gen func(*rand.Rand) S, elem func(*rand.Rand) E) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, v := gen(rng), randomSliceOf(rng, elem)
		i := rng.Intn(len(s)+2) - 1
		if rng.Intn(3) > 0 {
			i = rng.Intn(len(s) + 1)
		}
		before := snapshot(s, v)
		if i < 0 || i > len(s) {
			return sample{before: []any{before[0], i, before[1]}, after: []any{s, i, v}}
		}
		return sample{before: []any{before[0], i, before[1]}, after: []any{s, i, v}, results: []any{slices.Insert(s, i, v...)}}
	}
}

// boundCall calls Max or Min, which panic on an empty slice.
func boundCall[S ~[]E, E any](gen func(*rand.Rand) S, call func(S) E) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s := gen(rng)
		before := snapshot(s)
		if len(s) == 0 {
			return sample{before: before, after: []any{s}}
		}
		return sample{before: before, after: []any{s}, results: []any{call(s)}}
	}
}

// pairCall calls a function of two slices.
func pairCall[S ~[]E, E any](gen func(*rand.Rand) S, call func(S, S) []any) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		a, b := gen(rng), gen(rng)
		if rng.Intn(3) == 0 {
			b = slices.Clone(a)
		}
		before := snapshot(a, b)
		results := call(a, b)
		return sample{before: before, after: []any{a, b}, results: results}
	}
}

// genericHarnesses holds, for each shipped entry of a generic function, the
// instantiations it is tested at.
var genericHarnesses = map[string][]genericCase{
	"slices.Contains": {
		{targs: sliceOf(basic(types.Int)), harness: sliceValueCall(gen(smallInt), smallInt, func(s []int, v int) []any { return one(slices.Contains(s, v)) })},
		{targs: sliceOf(basic(types.String)), harness: sliceValueCall(gen(smallString), smallString, func(s []string, v string) []any { return one(slices.Contains(s, v)) })},
		{targs: sliceOf(pointerType), harness: sliceValueCall(gen(smallPointer), smallPointer, func(s []*harnessPoint, v *harnessPoint) []any { return one(slices.Contains(s, v)) })},
		{targs: idsArgs, harness: sliceValueCall(genIDs, smallInt, func(s harnessIDs, v int) []any { return one(slices.Contains(s, v)) })},
		{targs: sliceOf(pointType), refused: "is a struct, and a formula cannot compare a struct"},
		{targs: sliceOf(basic(types.Float64)), refused: "cannot be applied to float values"},
	},
	"slices.Index": {
		{targs: sliceOf(basic(types.Int)), harness: sliceValueCall(gen(smallInt), smallInt, func(s []int, v int) []any { return one(slices.Index(s, v)) })},
		{targs: sliceOf(basic(types.String)), harness: sliceValueCall(gen(smallString), smallString, func(s []string, v string) []any { return one(slices.Index(s, v)) })},
		{targs: sliceOf(pointerType), harness: sliceValueCall(gen(smallPointer), smallPointer, func(s []*harnessPoint, v *harnessPoint) []any { return one(slices.Index(s, v)) })},
		{targs: sliceOf(pointType), refused: "is a struct"},
	},
	"slices.ContainsFunc": {
		{targs: sliceOf(basic(types.Int)), harness: sliceFuncCall(gen(smallInt), "f", func(s []int, f func(int) bool) []any { return one(slices.ContainsFunc(s, f)) })},
		{targs: sliceOf(basic(types.String)), harness: sliceFuncCall(gen(smallString), "f", func(s []string, f func(string) bool) []any { return one(slices.ContainsFunc(s, f)) })},
		{targs: sliceOf(pointType), harness: sliceFuncCall(gen(smallPoint), "f", func(s []harnessPoint, f func(harnessPoint) bool) []any { return one(slices.ContainsFunc(s, f)) })},
		{targs: sliceOf(basic(types.Float64)), harness: sliceFuncCall(gen(smallFloat), "f", func(s []float64, f func(float64) bool) []any { return one(slices.ContainsFunc(s, f)) })},
	},
	"slices.IndexFunc": {
		{targs: sliceOf(basic(types.Int)), harness: sliceFuncCall(gen(smallInt), "f", func(s []int, f func(int) bool) []any { return one(slices.IndexFunc(s, f)) })},
		{targs: sliceOf(pointType), harness: sliceFuncCall(gen(smallPoint), "f", func(s []harnessPoint, f func(harnessPoint) bool) []any { return one(slices.IndexFunc(s, f)) })},
		{targs: sliceOf(basic(types.String)), harness: sliceFuncCall(gen(smallString), "f", func(s []string, f func(string) bool) []any { return one(slices.IndexFunc(s, f)) })},
	},
	"slices.Equal": {
		{targs: sliceOf(basic(types.Int)), harness: pairCall(gen(smallInt), func(a, b []int) []any { return one(slices.Equal(a, b)) })},
		{targs: sliceOf(basic(types.String)), harness: pairCall(gen(smallString), func(a, b []string) []any { return one(slices.Equal(a, b)) })},
		{targs: sliceOf(pointerType), harness: pairCall(gen(smallPointer), func(a, b []*harnessPoint) []any { return one(slices.Equal(a, b)) })},
		{targs: sliceOf(pointType), refused: "is a struct"},
		{targs: sliceOf(basic(types.Float64)), refused: "cannot be applied to float values"},
	},
	"slices.Clone": {
		{targs: sliceOf(basic(types.Int)), harness: sliceCall(gen(smallInt), func(s []int) []any { return one(slices.Clone(s)) })},
		{targs: sliceOf(basic(types.String)), harness: sliceCall(gen(smallString), func(s []string) []any { return one(slices.Clone(s)) })},
		{targs: sliceOf(pointType), harness: sliceCall(gen(smallPoint), func(s []harnessPoint) []any { return one(slices.Clone(s)) })},
		{targs: sliceOf(pointerType), harness: sliceCall(gen(smallPointer), func(s []*harnessPoint) []any { return one(slices.Clone(s)) })},
		{targs: sliceOf(basic(types.Float64)), harness: sliceCall(gen(smallFloat), func(s []float64) []any { return one(slices.Clone(s)) })},
		{targs: sliceOf(emptyType), harness: sliceCall(gen(anyEmpty), func(s []harnessEmpty) []any { return one(slices.Clone(s)) })},
		{targs: idsArgs, harness: sliceCall(genIDs, func(s harnessIDs) []any { return one(slices.Clone(s)) })},
	},
	"slices.Grow": {
		{targs: sliceOf(basic(types.Int)), harness: growCall(gen(smallInt))},
		{targs: sliceOf(basic(types.Uint8)), harness: growCall(gen(smallByte))},
		{targs: sliceOf(basic(types.String)), harness: growCall(gen(smallString))},
		{targs: sliceOf(pointType), harness: growCall(gen(smallPoint))},
		{targs: sliceOf(emptyType), harness: growCall(gen(anyEmpty))},
		{targs: idsArgs, harness: growCall(genIDs)},
	},
	"slices.Clip": {
		{targs: sliceOf(basic(types.Int)), harness: sliceCall(gen(smallInt), func(s []int) []any { return one(slices.Clip(s)) })},
		{targs: sliceOf(pointType), harness: sliceCall(gen(smallPoint), func(s []harnessPoint) []any { return one(slices.Clip(s)) })},
		{targs: sliceOf(emptyType), harness: sliceCall(gen(anyEmpty), func(s []harnessEmpty) []any { return one(slices.Clip(s)) })},
	},
	"slices.Delete": {
		{targs: sliceOf(basic(types.Int)), harness: deleteCall(gen(smallInt))},
		{targs: sliceOf(basic(types.String)), harness: deleteCall(gen(smallString))},
		{targs: sliceOf(pointType), harness: deleteCall(gen(smallPoint))},
		{targs: sliceOf(pointerType), harness: deleteCall(gen(smallPointer))},
	},
	"slices.DeleteFunc": {
		{targs: sliceOf(basic(types.Int)), harness: sliceFuncCall(gen(smallInt), "del", func(s []int, f func(int) bool) []any { return one(slices.DeleteFunc(s, f)) })},
		{targs: sliceOf(basic(types.String)), harness: sliceFuncCall(gen(smallString), "del", func(s []string, f func(string) bool) []any { return one(slices.DeleteFunc(s, f)) })},
		{targs: sliceOf(pointType), harness: sliceFuncCall(gen(smallPoint), "del", func(s []harnessPoint, f func(harnessPoint) bool) []any { return one(slices.DeleteFunc(s, f)) })},
	},
	"slices.Insert": {
		{targs: sliceOf(basic(types.Int)), harness: insertCall(gen(smallInt), smallInt)},
		{targs: sliceOf(basic(types.String)), harness: insertCall(gen(smallString), smallString)},
		{targs: sliceOf(pointType), harness: insertCall(gen(smallPoint), smallPoint)},
		{targs: sliceOf(emptyType), harness: insertCall(gen(anyEmpty), anyEmpty)},
	},
	"slices.Reverse": {
		{targs: sliceOf(basic(types.Int)), harness: sliceCall(gen(smallInt), func(s []int) []any { slices.Reverse(s); return nil })},
		{targs: sliceOf(pointType), harness: sliceCall(gen(smallPoint), func(s []harnessPoint) []any { slices.Reverse(s); return nil })},
	},
	"slices.Sort": {
		{targs: sliceOf(basic(types.Int)), harness: sliceCall(gen(smallInt), func(s []int) []any { slices.Sort(s); return nil })},
		{targs: sliceOf(basic(types.String)), harness: sliceCall(gen(smallString), func(s []string) []any { slices.Sort(s); return nil })},
		{targs: sliceOf(basic(types.Float64)), harness: sliceCall(gen(smallFloat), func(s []float64) []any { slices.Sort(s); return nil })},
		{targs: idsArgs, harness: sliceCall(genIDs, func(s harnessIDs) []any { slices.Sort(s); return nil })},
	},
	"slices.BinarySearch": {
		{targs: sliceOf(basic(types.Int)), harness: sliceValueCall(sortedGen(smallInt), smallInt, func(s []int, v int) []any {
			i, found := slices.BinarySearch(s, v)
			return []any{i, found}
		})},
		{targs: sliceOf(basic(types.Int64)), harness: sliceValueCall(sortedGen(smallInt64), smallInt64, func(s []int64, v int64) []any {
			i, found := slices.BinarySearch(s, v)
			return []any{i, found}
		})},
		{targs: sliceOf(basic(types.String)), refused: "cannot be applied to string or slice values; a formula has no order of them"},
		{targs: sliceOf(basic(types.Float64)), refused: "cannot be applied to float values"},
	},
	"slices.Max": {
		{targs: sliceOf(basic(types.Int)), harness: boundCall(gen(smallInt), slices.Max[[]int])},
		{targs: sliceOf(basic(types.Uint8)), harness: boundCall(gen(smallByte), slices.Max[[]uint8])},
		{targs: sliceOf(basic(types.String)), refused: "a formula has no order of them"},
		{targs: sliceOf(basic(types.Float64)), refused: "cannot be applied to float values"},
	},
	"slices.Min": {
		{targs: sliceOf(basic(types.Int)), harness: boundCall(gen(smallInt), slices.Min[[]int])},
		{targs: sliceOf(basic(types.Int64)), harness: boundCall(gen(smallInt64), slices.Min[[]int64])},
		{targs: sliceOf(basic(types.String)), refused: "a formula has no order of them"},
	},
	"slices.Compact": {
		{targs: sliceOf(basic(types.Int)), harness: sliceCall(gen(smallInt), func(s []int) []any { return one(slices.Compact(s)) })},
		{targs: sliceOf(basic(types.String)), harness: sliceCall(gen(smallString), func(s []string) []any { return one(slices.Compact(s)) })},
		{targs: sliceOf(pointType), harness: sliceCall(gen(smallPoint), func(s []harnessPoint) []any { return one(slices.Compact(s)) })},
		{targs: sliceOf(basic(types.Float64)), harness: sliceCall(gen(smallFloat), func(s []float64) []any { return one(slices.Compact(s)) })},
	},
}

// checkGenericEntry tests the shipped entry of a generic function at each
// instantiation of its harnesses. Each condition of an ensures must hold in
// some call at some instantiation.
func checkGenericEntry(t *testing.T, pv *pkgVerifier, key string, generic *types.Func) {
	cases, ok := genericHarnesses[key]
	if !ok {
		t.Fatalf("no harness calls %s; add its instantiations to genericHarnesses", key)
	}
	kit := newHarnessTypes(pv.pass.Pkg)
	refusedAt, usedAt := 0, 0
	pooled := map[string][]int{}
	for _, c := range cases {
		targs := c.targs(kit)
		sig, err := types.Instantiate(nil, generic.Type(), targs, true)
		if err != nil {
			t.Fatalf("instantiate %s at %v: %v", key, targs, err)
		}
		inst := pv.instantiate(generic, targs, sig.(*types.Signature))
		at := pv.typeArgsNamed(inst)
		fn := pv.trustedContract(inst)
		if c.refused != "" {
			refusedAt++
			if !slices.ContainsFunc(fn.defects, func(d string) bool { return strings.Contains(d, c.refused) }) {
				t.Errorf("at %s the contract must be refused with %q, and its defects are %q", at, c.refused, fn.defects)
			}
			continue
		}
		usedAt++
		for _, defect := range fn.defects {
			t.Errorf("at %s the contract cannot be used: %s", at, defect)
		}
		if t.Failed() {
			continue
		}
		met := coverage{}
		checkContract(t, pv, key+" at "+at, fn, c.harness, met)
		for clause, counts := range met {
			if pooled[clause.text] == nil {
				pooled[clause.text] = make([]int, len(counts))
			}
			for i, n := range counts {
				pooled[clause.text][i] += n
			}
		}
	}
	if usedAt < 2 {
		t.Errorf("the harness of %s tests %d instantiations at which the contract is used; test it at several", key, usedAt)
	}
	for text, counts := range pooled {
		for j, n := range counts {
			if n == 0 {
				t.Errorf("no call at any instantiation met condition %d of ensures %q; give the harness inputs that meet it", j+1, text)
			}
		}
	}
	_ = refusedAt
}

// groundSlice converts a slice of any element type to the term that denotes
// it: a sequence of what each element denotes. An element of which no
// formula of an entry can read anything, as a struct, is a constant the
// evaluator cannot read.
func (g *grounder) groundSlice(v reflect.Value) *logic.Term {
	elem := func(e reflect.Value) *logic.Term {
		if k := e.Kind(); k == reflect.Struct || k == reflect.Float32 || k == reflect.Float64 {
			// No formula can read a struct or a float element of a
			// generic function's slice (a struct is refused whole, and a
			// float is opaque), so what stands for it is never read.
			return logic.IntLit(0)
		}
		return g.groundTerm(e.Interface())
	}
	var zero *logic.Term
	switch v.Type().Elem().Kind() {
	case reflect.Struct:
		zero = logic.IntLit(0)
	case reflect.Pointer:
		zero = logic.RefLit(0)
	case reflect.String:
		zero = logic.Bytes("")
	default:
		zero = logic.IntLit(0)
	}
	seq := logic.Fill(logic.IntLit(0), zero)
	for i := range v.Len() {
		seq = logic.Push(seq, elem(v.Index(i)))
	}
	return seq
}

// pointerRef numbers the pointers the grounder meets, one number for each
// address, so that pointers compare as they do in Go.
func (g *grounder) pointerRef(p uintptr) *logic.Term {
	if g.pointers == nil {
		g.pointers = map[uintptr]int64{}
	}
	if _, ok := g.pointers[p]; !ok {
		g.pointers[p] = int64(len(g.pointers) + 1)
	}
	return logic.RefLit(g.pointers[p])
}

// givenSliceOf answers cap(A) and A = nil of a parameter or a result of a
// call from the real slice; see specEnv.givenSlice.
func givenSliceOf(t *testing.T, fn *funcInfo, call sample) func(name string, last logic.Step, when logic.When) (*logic.Term, error) {
	return func(name string, last logic.Step, when logic.When) (*logic.Term, error) {
		var value any
		if i, isResult := fn.resultNames[name]; isResult {
			value = call.results[i]
		}
		// A slice is passed by value, so its capacity and whether it is nil
		// are the same before and after the call.
		for i, param := range fn.params {
			if param.Name() == name {
				value = call.after[i]
			}
		}
		v := reflect.ValueOf(value)
		switch {
		case v.Kind() != reflect.Slice && last.Nil:
			// A comparison with nil of anything else is resolved as for
			// any other value.
			return nil, logic.NotSlice
		case v.Kind() != reflect.Slice:
			return nil, fmt.Errorf("cap(%s): %s is not a slice", name, name)
		}
		switch {
		case last.Cap:
			return logic.BigLit(big.NewInt(int64(v.Cap()))), nil
		case last.Nil:
			return logic.BoolLit(v.IsNil()), nil
		}
		t.Fatalf("the harness cannot tell %v of %s", last, name)
		return nil, nil
	}
}
