// Package sorts sorts slices with the shipped entries of slices.SortFunc
// and slices.SortStableFunc, which claim no order: the slice holds the
// elements it held, where a formula can compare them.
package sorts

import (
	"cmp"
	"slices"
)

type task struct {
	name string
	due  int
}

// ByDue sorts pointers that are not nil, which stay not nil, with a
// comparison that tests for nil all the same.
//
// @Requires Forall i in [0, |ts|) : ts[i] != nil
// @Modifies ts
// @Ensures Forall i in [0, |ts|) : ts'[i] != nil
func ByDue(ts []*task) {
	slices.SortFunc(ts, func(a, b *task) int {
		if a == nil || b == nil {
			return 0
		}
		return cmp.Compare(a.due, b.due)
	})
}

// Unguarded follows what the comparison is handed with no nil test: each
// is an element the slice held when the sort was called.
//
// @Requires Forall i in [0, |ts|) : ts[i] != nil
// @Modifies ts
// @Ensures Forall i in [0, |ts|) : ts'[i] != nil
func Unguarded(ts []*task) {
	slices.SortFunc(ts, func(a, b *task) int { return cmp.Compare(a.due, b.due) })
}

// UnguardedStable sorts a slice after an append, by a comparison with no
// nil test.
//
// @Requires Forall i in [0, |ts|) : ts[i] != nil
// @Requires |ts| < 1000 And t != nil
// @Modifies ts
// @Ensures |r| = |ts| + 1
func UnguardedStable(ts []*task, t *task) (r []*task) {
	r = append(ts, t)
	slices.SortStableFunc(r, func(a, b *task) int { return cmp.Compare(a.due, b.due) })
	return r
}

// MaybeNil sorts pointers of which nothing says they are not nil.
//
// @Modifies ts
// @Ensures True
func MaybeNil(ts []*task) {
	slices.SortFunc(ts, func(a, b *task) int { return cmp.Compare(a.due, b.due) }) // want `pointer may be nil, in the function literal run by slices.SortFunc` `pointer may be nil, in the function literal run by slices.SortFunc`
}

// FirstDue reads every element after the sort with no nil test.
//
// @Requires Forall i in [0, |ts|) : ts[i] != nil
// @Modifies ts
// @Ensures True
func FirstDue(ts []*task) (due int) {
	slices.SortStableFunc(ts, func(a, b *task) int {
		if a == nil || b == nil {
			return 0
		}
		return cmp.Compare(a.due, b.due)
	})
	for _, t := range ts {
		due = t.due
	}
	return due
}

// Bounded sorts numbers in a range, which stay in it.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 9
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : 0 <= xs'[i] <= 9
func Bounded(xs []int) {
	slices.SortFunc(xs, func(a, b int) int { return cmp.Compare(b, a) })
}

// Inconsistent sorts with a comparison that is no ordering: the elements
// are still those that were there.
//
// @Requires Forall i in [0, |xs|) : xs[i] = 4
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : xs'[i] = 4
func Inconsistent(xs []int) {
	slices.SortFunc(xs, func(a, b int) int { return 1 })
}

// Structs sorts structs, of whose elements nothing is known after.
//
// @Requires Forall i in [0, |ts|) : ts[i].due >= 0
// @Modifies ts
// @Ensures Forall i in [0, |ts|) : ts'[i].due >= 0
func Structs(ts []task) {
	slices.SortFunc(ts, func(a, b task) int { return cmp.Compare(a.due, b.due) })
} // want `postcondition may not hold: Forall i in \[0, \|ts\|\) : ts'\[i\].due >= 0`

// Writes writes the slice while it is sorted.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func Writes(xs []int) {
	slices.SortFunc(xs, func(a, b int) int {
		xs[0] = a // want `xs\[0\] is assigned, which slices.SortFunc may write itself while it runs the function it is handed`
		return 0
	})
}

// WritesByClosure writes the slice through a recursive closure that the
// comparison calls (F6 of the design review).
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func WritesByClosure(xs []int) {
	var reset func()
	// @Requires |xs| > 0
	// @Modifies xs
	reset = func() {
		xs[0] = 0
	}
	slices.SortFunc(xs, func(a, b int) int {
		reset() // want `the closure reset may modify xs, which slices.SortFunc may write itself`
		return 0
	})
}

// sortThen hands slices.SortFunc a comparison that calls f, which may
// write the array it made, which SortFunc writes (F2).
//
// @Calls f()
// @Ensures True
func sortThen(f func()) {
	ys := make([]int, 3)
	slices.SortFunc(ys, func(a, b int) int {
		f() // want `f may write what slices.SortFunc may write itself`
		return 0
	})
}

// sortKept hands slices.SortFunc a comparison that calls f while it sorts
// what the function may write itself, which f may not write.
//
// @Calls f()
// @Modifies ys
// @Ensures True
func sortKept(ys []int, f func()) {
	slices.SortFunc(ys, func(a, b int) int {
		f()
		return 0
	})
}
