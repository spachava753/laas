package vego

import (
	"cmp"
	"fmt"
	"go/types"
	"maps"
	"math/big"
	"math/rand"
	"reflect"
	"slices"
	"sort"
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
	harnessPoint  struct{ X, Y int }
	harnessIDs    []int
	harnessEmpty  struct{}
	harnessCounts map[string]int
	// harnessLevel is a named integer with methods.
	harnessLevel int
)

// The methods of the type arguments fail the test when called: the shipped
// entries of generic functions claim to run none.
func calledMethod(name string) {
	calledMethods = append(calledMethods, name)
	panic("a shipped generic function called the method " + name + " of a type argument, which its entry claims it does not")
}

// calledMethods records each call of a method of a type argument of the
// harness, also one whose panic something recovered.
var calledMethods []string

func (harnessLevel) String() string          { calledMethod("String"); return "" }
func (harnessLevel) Error() string           { calledMethod("Error"); return "" }
func (*harnessLevel) Format(fmt.State, rune) { calledMethod("Format") }
func (*harnessLevel) GoString() string       { calledMethod("GoString"); return "" }
func (harnessPoint) String() string          { calledMethod("String"); return "" }
func (harnessPoint) Error() string           { calledMethod("Error"); return "" }
func (*harnessPoint) Format(fmt.State, rune) { calledMethod("Format") }
func (*harnessPoint) GoString() string       { calledMethod("GoString"); return "" }

// harnessTypes are the types of the type arguments of the harness.
type harnessTypes struct {
	point, ids, empty, counts, level types.Type
}

func newHarnessTypes(pkg *types.Package) *harnessTypes {
	named := func(name string, underlying types.Type) types.Type {
		return types.NewNamed(types.NewTypeName(0, pkg, name, nil), underlying, nil)
	}
	intT := types.Typ[types.Int]
	field := func(name string) *types.Var { return types.NewField(0, pkg, name, intT, false) }
	// The types with methods have them here too, so that the claim under
	// asserts is what lets a call of them through.
	withMethods := func(t types.Type) types.Type {
		named := t.(*types.Named)
		str := types.NewSignatureType(nil, nil, nil, nil, types.NewTuple(types.NewVar(0, pkg, "", types.Typ[types.String])), false)
		for _, m := range []struct {
			name    string
			pointer bool
		}{{"String", false}, {"Error", false}, {"GoString", true}} {
			var recv types.Type = named
			if m.pointer {
				recv = types.NewPointer(named)
			}
			sig := types.NewSignatureType(types.NewVar(0, pkg, "", recv), nil, nil, nil, str.Results(), false)
			named.AddMethod(types.NewFunc(0, pkg, m.name, sig))
		}
		return named
	}
	return &harnessTypes{
		level:  withMethods(named("harnessLevel", intT)),
		point:  withMethods(named("harnessPoint", types.NewStruct([]*types.Var{field("X"), field("Y")}, nil))),
		ids:    named("harnessIDs", types.NewSlice(intT)),
		empty:  named("harnessEmpty", types.NewStruct(nil, nil)),
		counts: named("harnessCounts", types.NewMap(types.Typ[types.String], intT)),
	}
}

// pointPool is the memory the pointers of the harness point to, so that two
// elements are often the same pointer.
var pointPool = []*harnessPoint{{1, 2}, {1, 2}, {3, 4}}

// Elements of each type, from few values so that elements are often equal.
func smallInt(rng *rand.Rand) int       { return rng.Intn(4) - 1 }
func smallByte(rng *rand.Rand) byte     { return byte(rng.Intn(3)) * 120 }
func smallString(rng *rand.Rand) string { return []string{"", "a", "b", "ab"}[rng.Intn(4)] }
func smallPoint(rng *rand.Rand) harnessPoint {
	return harnessPoint{rng.Intn(2), rng.Intn(2)}
}
func smallPointer(rng *rand.Rand) *harnessPoint {
	return pointPool[rng.Intn(len(pointPool))]
}
func smallFloat(rng *rand.Rand) float64 { return randomFloat(rng) }
func anyEmpty(*rand.Rand) harnessEmpty  { return harnessEmpty{} }

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

// sliceCmpCall calls a function that sorts a slice by a comparison, with
// one that answers at random, so that it is no ordering at all, and records
// what it is given.
func sliceCmpCall[S ~[]E, E any](gen func(*rand.Rand) S, call func(S, func(a, b E) int)) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, calls, during := gen(rng), map[string][][]any{}, map[string][][]any{}
		cmp := func(a, b E) int {
			calls["cmp"] = append(calls["cmp"], []any{a, b})
			during["cmp"] = append(during["cmp"], []any{snapshot(s)[0], nil})
			return rng.Intn(3) - 1
		}
		before := snapshot(s)
		call(s, cmp)
		return sample{before: []any{before[0], cmp}, after: []any{s, cmp}, calls: calls, during: during}
	}
}

// sliceLessCall calls sort.Slice or sort.SliceStable, through the view its
// entry is written against, with a less that answers at random and records
// the indices it is given.
func sliceLessCall[S ~[]E, E any](gen func(*rand.Rand) S, call func(S, func(i, j int) bool)) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, calls, during := gen(rng), map[string][][]any{}, map[string][][]any{}
		less := func(i, j int) bool {
			calls["less"] = append(calls["less"], []any{i, j})
			during["less"] = append(during["less"], []any{snapshot(s)[0], nil})
			return rng.Intn(2) == 0
		}
		before := snapshot(s)
		call(s, less)
		return sample{before: []any{before[0], less}, after: []any{s, less}, calls: calls, during: during}
	}
}

func gen[E any](elem func(*rand.Rand) E) func(*rand.Rand) []E {
	return func(rng *rand.Rand) []E { return randomSliceOf(rng, elem) }
}

func genIDs(rng *rand.Rand) harnessIDs { return harnessIDs(randomSliceOf(rng, smallInt)) }

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

// randomMapOf returns a map of up to five keys, at times nil and at times
// empty.
func randomMapOf[K comparable, V any](rng *rand.Rand, key func(*rand.Rand) K, value func(*rand.Rand) V) map[K]V {
	if rng.Intn(6) == 0 {
		return nil
	}
	m := map[K]V{}
	for range rng.Intn(6) {
		m[key(rng)] = value(rng)
	}
	return m
}

func mapGen[K comparable, V any](key func(*rand.Rand) K, value func(*rand.Rand) V) func(*rand.Rand) map[K]V {
	return func(rng *rand.Rand) map[K]V { return randomMapOf(rng, key, value) }
}

func countsGen(rng *rand.Rand) harnessCounts {
	return harnessCounts(randomMapOf(rng, smallString, smallInt))
}

// copyCall calls maps.Copy, but not into a nil map with keys to copy,
// which panics, and not with one map as both, which writes what src is;
// the corpus holds a call of that kind.
func copyCall[M ~map[K]V, K comparable, V any](gen func(*rand.Rand) M) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		dst, src := gen(rng), gen(rng)
		if dst == nil && rng.Intn(2) == 0 {
			dst = M{}
		}
		before := snapshot(dst, src)
		if dst != nil || len(src) == 0 {
			maps.Copy(dst, src)
		}
		return sample{before: before, after: []any{dst, src}}
	}
}

// deleteFuncCall calls maps.DeleteFunc with a function that answers at
// random and records what it is given.
func deleteFuncCall[M ~map[K]V, K comparable, V any](gen func(*rand.Rand) M) func(*rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		m, calls := gen(rng), map[string][][]any{}
		del := func(k K, v V) bool {
			calls["del"] = append(calls["del"], []any{k, v})
			return rng.Intn(2) == 0
		}
		before := snapshot(m)
		maps.DeleteFunc(m, del)
		return sample{before: []any{before[0], del}, after: []any{m, del}, calls: calls}
	}
}

// harnessClasses are the kinds of type argument every shipped entry of a
// generic function is tested at, where its constraint admits them: for a
// function of a slice or a map the class is that of the element or the
// value. Each must have a harness or the refusal the entry draws there.
var harnessClasses = []string{"int", "uint8", "level", "bool", "string", "pointer", "zero pointer", "struct", "zero struct", "float64", "named slice"}

// keyClasses are the kinds of key every entry of a function of a map is
// tested at, with integers as values. A key of another kind makes a map
// that vego does not model.
var keyClasses = []string{"int", "uint8", "level", "string", "bool", "pointer", "struct", "float64"}

// classType is the type of a class in the package of the shipped verifier.
func (h *harnessTypes) classType(class string) types.Type {
	switch class {
	case "int":
		return types.Typ[types.Int]
	case "uint8":
		return types.Typ[types.Uint8]
	case "level":
		return h.level
	case "bool":
		return types.Typ[types.Bool]
	case "string":
		return types.Typ[types.String]
	case "pointer":
		return types.NewPointer(h.point)
	case "zero pointer":
		return types.NewPointer(h.empty)
	case "struct":
		return h.point
	case "zero struct":
		return h.empty
	case "float64":
		return types.Typ[types.Float64]
	}
	panic("no type for the class " + class)
}

// typeArgs gives the type arguments of a generic function at a class: of a
// function of a map, the class is that of the value, with keys of type
// key, and the named type is harnessCounts; of one of a slice, the class
// is that of the element, and the named type is harnessIDs; and of any
// other, the class is the type, and there is no named one.
func (h *harnessTypes) typeArgs(generic *types.Func, class, key string) []types.Type {
	params := generic.Type().(*types.Signature).TypeParams()
	switch core := coreType(params.At(0)).(type) {
	case *types.Map:
		// Of a function of a map, a named type is the named map type
		// harnessCounts.
		var m, k, v types.Type = h.counts, types.Typ[types.String], types.Typ[types.Int]
		if class != "named slice" {
			k, v = h.classType(key), h.classType(class)
			m = types.NewMap(k, v)
		}
		if params.Len() == 4 {
			return []types.Type{m, m, k, v}
		}
		return []types.Type{m, k, v}
	case *types.Slice:
		if class == "named slice" {
			return []types.Type{h.ids, types.Typ[types.Int]}
		}
		e := h.classType(class)
		return []types.Type{types.NewSlice(e), e}
	default:
		_ = core
		if class == "named slice" {
			return nil
		}
		return []types.Type{h.classType(class)}
	}
}

// Elements of the classes of the harness.
func smallBool(rng *rand.Rand) bool                 { return rng.Intn(2) == 0 }
func smallLevel(rng *rand.Rand) harnessLevel        { return harnessLevel(rng.Intn(3)) }
func smallZeroPointer(rng *rand.Rand) *harnessEmpty { return &harnessEmpty{} }

// harnessAt returns the harness of an entry at a class, with string keys
// for a function of a map.
func harnessAt(key, class string) func(*rand.Rand) sample {
	switch class {
	case "int":
		return orderedHarness(key, gen(smallInt), smallInt)
	case "uint8":
		return orderedHarness(key, gen(smallByte), smallByte)
	case "level":
		return orderedHarness(key, gen(smallLevel), smallLevel)
	case "string":
		return orderedHarness(key, gen(smallString), smallString)
	case "float64":
		return orderedHarness(key, gen(smallFloat), smallFloat)
	case "named slice":
		if strings.HasPrefix(key, "maps.") {
			return mapHarness(key, countsGen)
		}
		return orderedHarness(key, genIDs, smallInt)
	case "bool":
		return comparableHarness(key, gen(smallBool), smallBool)
	case "pointer":
		return comparableHarness(key, gen(smallPointer), smallPointer)
	case "zero pointer":
		return comparableHarness(key, gen(smallZeroPointer), smallZeroPointer)
	case "struct":
		return comparableHarness(key, gen(smallPoint), smallPoint)
	case "zero struct":
		return comparableHarness(key, gen(anyEmpty), anyEmpty)
	}
	return nil
}

// keyHarnessAt returns the harness of an entry of a function of a map at a
// class of key, with integers as values.
func keyHarnessAt(key, class string) func(*rand.Rand) sample {
	switch class {
	case "int":
		return mapHarness(key, mapGen(smallInt, smallInt))
	case "uint8":
		return mapHarness(key, mapGen(smallByte, smallInt))
	case "level":
		return mapHarness(key, mapGen(smallLevel, smallInt))
	case "string":
		return mapHarness(key, mapGen(smallString, smallInt))
	case "bool":
		return mapHarness(key, mapGen(smallBool, smallInt))
	}
	return nil
}

// sortedOf is a generator of slices sorted three times in four.
func sortedOf[S ~[]E, E cmp.Ordered](gen func(*rand.Rand) S) func(*rand.Rand) S {
	return func(rng *rand.Rand) S {
		s := gen(rng)
		if rng.Intn(4) > 0 {
			slices.Sort(s)
		}
		return s
	}
}

// orderedHarness is the harness of an entry at an ordered element type.
func orderedHarness[S ~[]E, E cmp.Ordered](key string, gen func(*rand.Rand) S, elem func(*rand.Rand) E) func(*rand.Rand) sample {
	switch key {
	case "slices.Sort":
		return sliceCall(gen, func(s S) []any { slices.Sort(s); return nil })
	case "slices.BinarySearch":
		return sliceValueCall(sortedOf(gen), elem, func(s S, v E) []any {
			i, found := slices.BinarySearch(s, v)
			return []any{i, found}
		})
	case "slices.Max":
		return boundCall(gen, slices.Max[S])
	case "slices.Min":
		return boundCall(gen, slices.Min[S])
	case "cmp.Compare":
		// Two values that are often equal.
		return func(rng *rand.Rand) sample {
			x, y := elem(rng), elem(rng)
			return sample{before: []any{x, y}, results: []any{cmp.Compare(x, y)}}
		}
	}
	return comparableHarness(key, gen, elem)
}

// comparableHarness is the harness of an entry at a comparable element
// type.
func comparableHarness[S ~[]E, E comparable](key string, gen func(*rand.Rand) S, elem func(*rand.Rand) E) func(*rand.Rand) sample {
	switch key {
	case "slices.Contains":
		return sliceValueCall(gen, elem, func(s S, v E) []any { return one(slices.Contains(s, v)) })
	case "slices.Index":
		return sliceValueCall(gen, elem, func(s S, v E) []any { return one(slices.Index(s, v)) })
	case "slices.Equal":
		return pairCall(gen, func(a, b S) []any { return one(slices.Equal(a, b)) })
	case "slices.Compact":
		return sliceCall(gen, func(s S) []any { return one(slices.Compact(s)) })
	}
	return anyHarness(key, gen, elem)
}

// anyHarness is the harness of an entry at any element type.
func anyHarness[S ~[]E, E any](key string, gen func(*rand.Rand) S, elem func(*rand.Rand) E) func(*rand.Rand) sample {
	switch key {
	case "slices.ContainsFunc":
		return sliceFuncCall(gen, "f", func(s S, f func(E) bool) []any { return one(slices.ContainsFunc(s, f)) })
	case "slices.IndexFunc":
		return sliceFuncCall(gen, "f", func(s S, f func(E) bool) []any { return one(slices.IndexFunc(s, f)) })
	case "slices.DeleteFunc":
		return sliceFuncCall(gen, "del", func(s S, f func(E) bool) []any { return one(slices.DeleteFunc(s, f)) })
	case "slices.SortFunc":
		return sliceCmpCall(gen, func(s S, cmp func(a, b E) int) { slices.SortFunc(s, cmp) })
	case "slices.SortStableFunc":
		return sliceCmpCall(gen, func(s S, cmp func(a, b E) int) { slices.SortStableFunc(s, cmp) })
	case "sort.Slice":
		return sliceLessCall(gen, func(s S, less func(i, j int) bool) { sort.Slice(s, less) })
	case "sort.SliceStable":
		return sliceLessCall(gen, func(s S, less func(i, j int) bool) { sort.SliceStable(s, less) })
	case "slices.Clone":
		return sliceCall(gen, func(s S) []any { return one(slices.Clone(s)) })
	case "slices.Clip":
		return sliceCall(gen, func(s S) []any { return one(slices.Clip(s)) })
	case "slices.Reverse":
		return sliceCall(gen, func(s S) []any { slices.Reverse(s); return nil })
	case "slices.Grow":
		return growCall(gen)
	case "slices.Delete":
		return deleteCall(gen)
	case "slices.Insert":
		return insertCall(gen, elem)
	}
	return mapHarness(key, mapGen(smallString, elem))
}

// mapHarness is the harness of an entry of a function of a map.
func mapHarness[M ~map[K]V, K comparable, V any](key string, gen func(*rand.Rand) M) func(*rand.Rand) sample {
	switch key {
	case "maps.Clone":
		return func(rng *rand.Rand) sample {
			m := gen(rng)
			before := snapshot(m)
			return sample{before: before, after: []any{m}, results: []any{maps.Clone(m)}}
		}
	case "maps.Copy":
		return copyCall(gen)
	case "maps.DeleteFunc":
		return deleteFuncCall(gen)
	}
	return nil
}

// refusedAt returns a part of the defect the contract of an entry has at a
// class, or "" where it must be usable.
func refusedAt(key, class string) string {
	equality := []string{"slices.Contains", "slices.Index", "slices.Equal"}
	order := []string{"slices.Max", "slices.Min", "slices.BinarySearch"}
	switch {
	case slices.Contains(equality, key) && (class == "struct" || class == "zero struct"):
		return "is a struct, and a formula cannot compare a struct"
	case slices.Contains(equality, key) && class == "zero pointer":
		return "pointers to values of size zero may or may not be equal"
	case (slices.Contains(equality, key) || slices.Contains(order, key) || key == "cmp.Compare") && class == "float64":
		return "cannot be applied to float values"
	case slices.Contains(order, key) && class == "string":
		return "a formula has no order of them"
	}
	return ""
}

// checkGenericEntry tests the shipped entry of a generic function at each
// class of type argument its constraint admits: by its harness where the
// contract must be usable, and by its defect where it must be refused. The
// type arguments with methods, harnessLevel and harnessPoint, fail the test
// if a method is called, as the entry claims under asserts that the
// function runs none; that claim is also checked to be there. Each
// condition of an ensures must hold in some call at some class.
func checkGenericEntry(t *testing.T, pv *pkgVerifier, key string, generic *types.Func) {
	kit := newHarnessTypes(pv.pass.Pkg)
	entry := pv.entryFor(key)
	pooled := map[string][]int{}
	usedAt := 0
	check := func(at string, targs []types.Type, harness func(*rand.Rand) sample, refused, typeRefused string) {
		sig, err := types.Instantiate(nil, generic.Type(), targs, true)
		if err != nil {
			return // the constraint does not admit the class
		}
		inst := pv.instantiate(generic, targs, sig.(*types.Signature))
		if problem := pv.typeArgProblem(pv.instanceOf[inst], entry); problem != "" || typeRefused != "" {
			if typeRefused == "" || !strings.Contains(problem, typeRefused) {
				t.Errorf("at %s a call must be refused with %q, and its refusal is %q", at, typeRefused, problem)
			}
			return
		}
		fn := pv.trustedContract(inst)
		if refused != "" {
			if !slices.ContainsFunc(fn.defects, func(d string) bool { return strings.Contains(d, refused) }) {
				t.Errorf("at %s the contract must be refused with %q, and its defects are %q", at, refused, fn.defects)
			}
			return
		}
		for _, defect := range fn.defects {
			t.Errorf("at %s the contract cannot be used: %s", at, defect)
		}
		if harness == nil {
			t.Fatalf("no harness calls %s at %s", key, at)
		}
		if t.Failed() {
			return
		}
		usedAt++
		met := coverage{}
		calledMethods = nil
		checkContract(t, pv, key+" at "+at, fn, harness, met)
		if len(calledMethods) > 0 {
			t.Errorf("at %s %s called the methods %v of its type argument, which its entry claims under asserts it does not", at, key, calledMethods)
		}
		for clause, counts := range met {
			if pooled[clause.text] == nil {
				pooled[clause.text] = make([]int, len(counts))
			}
			for i, n := range counts {
				pooled[clause.text][i] += n
			}
		}
	}
	_, ofMap := coreType(generic.Type().(*types.Signature).TypeParams().At(0)).(*types.Map)
	for _, class := range harnessClasses {
		targs := kit.typeArgs(generic, class, "string")
		if targs == nil {
			continue
		}
		check(class, targs, harnessAt(key, class), refusedAt(key, class), "")
	}
	if ofMap {
		for _, class := range keyClasses {
			typeRefused := ""
			if keyHarnessAt(key, class) == nil {
				typeRefused = "a type that vego does not model"
			}
			check("keys of "+class, kit.typeArgs(generic, "int", class), keyHarnessAt(key, class), "", typeRefused)
		}
	}
	if usedAt < 2 {
		t.Errorf("%s is used at %d classes of type argument; it should be usable at several", key, usedAt)
	}
	for text, counts := range pooled {
		for j, n := range counts {
			if n == 0 {
				t.Errorf("no call at any class met condition %d of ensures %q; give the harness inputs that meet it", j+1, text)
			}
		}
	}
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
	case reflect.Bool:
		zero = logic.BoolLit(false)
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

// keysOfMap answers, of a real map, whether it has a key, as a read of the
// set of the numbers of its keys, or the sort of its keys, for a quantifier
// over them.
func keysOfMap(eval *evaluator, name string, when logic.When, v reflect.Value, last logic.Step) *logic.Term {
	keys := map[int64]bool{}
	for _, key := range v.MapKeys() {
		switch key.Kind() {
		case reflect.String:
			keys[eval.intern(key.String())] = true
		case reflect.Bool:
			keys[map[bool]int64{true: 1}[key.Bool()]] = true
		case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
			keys[int64(key.Uint())] = true
		default:
			keys[key.Int()] = true
		}
	}
	if last.Keys {
		switch v.Type().Key().Kind() {
		case reflect.String:
			return logic.Fill(logic.IntLit(0), logic.IntLit(0))
		case reflect.Bool:
			return logic.False()
		}
		return logic.IntLit(0)
	}
	// The numbers of the keys are recorded under the name of the
	// constant that stands for them.
	if eval.keysets == nil {
		eval.keysets = map[string]map[int64]bool{}
	}
	set := fmt.Sprintf("keys of %s %d", name, when)
	eval.keysets[set] = keys
	return logic.Select(logic.Const(set, logic.BoolSeq), mapKey(last.Index))
}

// givenSliceOf answers cap(A) and A = nil of a parameter or a result of a
// call from the real slice, |m| of a map, and has(m, k) and the sort of its
// keys from the real map; see specEnv.givenSlice.
func givenSliceOf(t *testing.T, fn *funcInfo, call sample, eval *evaluator) func(name string, last logic.Step, when logic.When) (*logic.Term, error) {
	return func(name string, last logic.Step, when logic.When) (*logic.Term, error) {
		var value any
		if i, isResult := fn.resultNames[name]; isResult {
			value = call.results[i]
		}
		// A slice is passed by value, so its capacity and whether it is nil
		// are the same before and after the call; a map is a reference,
		// whose keys before the call are those of its snapshot.
		for i, param := range fn.params {
			if param.Name() != name {
				continue
			}
			value = call.after[i]
			if snap, ok := call.before[i].(snapped); ok && when != logic.Primed && (last.Len || last.Has || last.Keys) {
				value = snap.value
			}
		}
		v := reflect.ValueOf(value)
		switch {
		case last.Len && v.Kind() == reflect.Map:
			return logic.IntLit(int64(v.Len())), nil
		case (last.Has || last.Keys) && v.Kind() == reflect.Map:
			return keysOfMap(eval, name, when, v, last), nil
		case last.Has || last.Keys:
			return nil, fmt.Errorf("%s is not a map", name)
		case last.Len:
			return nil, fmt.Errorf("|%s|: %s is not a map", name, name)
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

// TestComparesPrimed checks that an ensures under compares is held to what
// the entry modifies as any other ensures is (F26 of the review of step 3
// of F40): one that describes elements of a slice after the call while its
// modifies lists nothing is a defect, at an element type with cells.
func TestComparesPrimed(t *testing.T) {
	for _, c := range []struct {
		modifies string
		defect   bool
	}{{"[]", true}, {"[s]", false}} {
		pv, imports := shippedVerifier(t)
		pkg, err := imports.Import("slices")
		if err != nil {
			t.Fatal(err)
		}
		generic := pkg.Scope().Lookup("Reverse").(*types.Func)
		pv.projectTrust = parseTrustFile("vego/trusted/std/test.yaml", []byte("version: 1\ntrusted:\n  slices.Reverse:\n    reason: r\n"+
			"    asserts: {S: [], E: []}\n    modifies: "+c.modifies+"\n    compares:\n      - \"Forall i in [0, |s'|) : s'[i] = s[i]\"\n"), true)
		targs := []types.Type{types.NewSlice(types.Typ[types.Int]), types.Typ[types.Int]}
		sig, err := types.Instantiate(nil, generic.Type(), targs, true)
		if err != nil {
			t.Fatal(err)
		}
		fn := pv.trustedContract(pv.instantiate(generic, targs, sig.(*types.Signature)))
		found := slices.ContainsFunc(fn.defects, func(d string) bool { return strings.Contains(d, "drop the prime") })
		if found != c.defect {
			t.Errorf("with modifies %s, a defect that the compares clause describes s after the call is %v, want %v; defects %q", c.modifies, found, c.defect, fn.defects)
		}
	}
}
