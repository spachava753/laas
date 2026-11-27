// Package unsafep imports unsafe, so every field of its structs is
// addressable, and a pointer from Leak is one Keep must weigh (F2 of the
// design review of F42).
package unsafep

import "unsafe"

// S holds two numbers.
type S struct {
	m int
	n int
}

// Leak is not verified: it returns a pointer to s.n by the arithmetic that
// the documentation of package unsafe allows (pattern 3).
func Leak(s *S) *int {
	return (*int)(unsafe.Add(unsafe.Pointer(s), unsafe.Offsetof(s.n)))
}

// Keep writes what p points to and claims s.n unchanged.
//
// @Requires p != nil And s != nil
// @Modifies p
// @Ensures s.n' = s.n
func Keep(p *int, s *S) {
	*p = 7
} // want `vego: postcondition may not hold: s\.n' = s\.n`

// N reads n.
//
// @Requires s != nil
// @Ensures r = s.n
func N(s *S) (r int) {
	return s.n
}
