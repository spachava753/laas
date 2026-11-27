// Package addrunsafeslice imports unsafe, with no expression of type
// unsafe.Pointer: only the import decides that every field of its structs
// is addressable (F9 of the review of step 1a of F42).
package addrunsafeslice

import "unsafe"

// S holds two numbers.
type S struct{ m, n int }

// Leak is not verified: it reaches s.n through a slice that unsafe.Slice
// makes over s.m, with no expression of type unsafe.Pointer.
func Leak(s *S) *int {
	return &unsafe.Slice(&s.m, 2)[1]
}

// Keep writes what q points to and claims s.n unchanged.
//
// @Requires q != nil And s != nil
// @Modifies q
// @Ensures s.n' = s.n
func Keep(q *int, s *S) {
	*q = 7
} // want `vego: postcondition may not hold: s\.n' = s\.n`
