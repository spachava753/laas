package sorts

import "sort"

// The calls of sort.Slice and sort.SliceStable, read through the typed
// view of the static type of their argument (D4 of F40).

type byName []*task

// SliceByDue sorts pointers that are not nil by an index comparison,
// which stay not nil.
//
// @Requires Forall i in [0, |ts|) : ts[i] != nil
// @Modifies ts
// @Ensures Forall i in [0, |ts|) : ts'[i] != nil
func SliceByDue(ts []*task) {
	sort.Slice(ts, func(i, j int) bool {
		if ts[i] == nil || ts[j] == nil {
			return false
		}
		return ts[i].due < ts[j].due
	})
}

// SliceUnguarded indexes the slice it sorts with no nil test: at each call
// of less, each element is one the slice held when the sort was called.
//
// @Requires Forall i in [0, |ts|) : ts[i] != nil
// @Modifies ts
// @Ensures Forall i in [0, |ts|) : ts'[i] != nil
func SliceUnguarded(ts []*task) {
	sort.Slice(ts, func(i, j int) bool { return ts[i].due < ts[j].due })
}

// SliceTwice sorts one slice twice, by two keys.
//
// @Requires Forall i in [0, |ts|) : ts[i] != nil
// @Modifies ts
// @Ensures Forall i in [0, |ts|) : ts'[i] != nil
func SliceTwice(ts []*task) {
	sort.Slice(ts, func(i, j int) bool { return ts[i].name < ts[j].name })
	sort.SliceStable(ts, func(i, j int) bool { return ts[i].due < ts[j].due })
}

// SliceOther compares by another slice, which the sort does not hold and
// of whose elements nothing is known at the call.
//
// @Requires |us| = |ts| And Forall i in [0, |ts|) : ts[i] != nil
// @Modifies ts
// @Ensures True
func SliceOther(ts, us []*task) {
	sort.Slice(ts, func(i, j int) bool { return us[i].due < us[j].due }) // want `pointer may be nil \(Z3 reached its resource limit; -vego.rlimit raises it\), in the function literal run by sort.Slice` `pointer may be nil \(Z3 reached its resource limit; -vego.rlimit raises it\), in the function literal run by sort.Slice`
}

// StableNamed sorts a slice of a named type, which keeps its length.
//
// @Modifies ts
// @Ensures |ts'| = |ts|
func StableNamed(ts byName) {
	sort.SliceStable(ts, func(i, j int) bool {
		if ts[i] == nil || ts[j] == nil {
			return false
		}
		return ts[i].name < ts[j].name
	})
}

// SliceBounded sorts numbers in a range, which stay in it.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 9
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : 0 <= xs'[i] <= 9
func SliceBounded(xs []int) {
	sort.Slice(xs, func(i, j int) bool { return xs[i] > xs[j] })
}

// SliceNil sorts a nil slice of a type, which is a slice.
//
// @Ensures True
func SliceNil() {
	sort.Slice([]int(nil), func(i, j int) bool { return false })
}

// SliceStructs sorts structs, of whose elements nothing is known after.
//
// @Requires Forall i in [0, |ts|) : ts[i].due >= 0
// @Modifies ts
// @Ensures Forall i in [0, |ts|) : ts'[i].due >= 0
func SliceStructs(ts []task) {
	sort.Slice(ts, func(i, j int) bool { return ts[i].due < ts[j].due })
} // want `postcondition may not hold: Forall i in \[0, \|ts\|\) : ts'\[i\].due >= 0`

// SliceShorter compares by a slice shorter than the one sorted, whose
// indices less is handed.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func SliceShorter(xs []int) {
	head := xs[:1]
	sort.Slice(xs, func(i, j int) bool { return head[i] < head[j] }) // want `index may be out of range, in the function literal run by sort.Slice` `index may be out of range, in the function literal run by sort.Slice`
}

// SliceWrites writes the slice while it is sorted.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func SliceWrites(xs []int) {
	sort.Slice(xs, func(i, j int) bool {
		xs[i] = 0 // want `xs\[i\] is assigned, which sort.Slice may write itself while it runs the function it is handed`
		return false
	})
}

// SliceAny sorts what an any holds, whose type vego does not know.
//
// @Ensures True
func SliceAny(v any) {
	sort.Slice(v, func(i, j int) bool { return false }) // want `cannot verify SliceAny: it calls sort.Slice with v of type any, which is not a slice`
}

// SliceUntypedNil sorts nil.
//
// @Ensures True
func SliceUntypedNil() {
	sort.Slice(nil, func(i, j int) bool { return false }) // want `cannot verify SliceUntypedNil: it calls sort.Slice with nil, which is not a slice`
}

// SliceArray sorts a pointer to an array, on which sort.Slice panics.
//
// @Ensures True
func SliceArray() {
	arr := [3]int{3, 1, 2}
	sort.SliceStable(&arr, func(i, j int) bool { return arr[i] < arr[j] }) // want `cannot verify SliceArray: it calls sort.SliceStable with &arr of type \*\[3\]int, which is not a slice`
}

type ranked []int

// Sort sorts its receiver. sort.Slice is handed a ranked, whose methods
// its entry claims under asserts it runs none of, so the call is no edge
// to this method, which would need a Variant.
//
// @Modifies r
// @Ensures |r'| = |r|
func (r ranked) Sort() {
	sort.Slice(r, func(i, j int) bool { return r[i] < r[j] })
}
