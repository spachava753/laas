// Package sliceviewp writes an element of a slice and claims a field of a
// struct unchanged, which holds unless code that is not verified makes a
// slice over the struct's fields, as sliceviewq does with unsafe.Slice;
// "What a proof assumes" excludes that (F10 of the review of step 1a of
// F42).
package sliceviewp

// S holds two exported numbers.
type S struct{ M, N int }

// Both writes an element of xs and claims s.N unchanged.
//
// @Requires s != nil And |xs| > 1
// @Modifies xs
// @Ensures s.N' = s.N
func Both(xs []int, s *S) {
	xs[1] = 7
}
