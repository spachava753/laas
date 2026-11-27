// Package reflectp does not import unsafe, but holds an expression of type
// unsafe.Pointer, which reflect's UnsafePointer gives, so every field of
// its structs is addressable (F2 of the design review of F42).
package reflectp

import "reflect"

// S holds two numbers.
type S struct {
	m int
	n int
}

// Leak is not verified and does not import unsafe: it returns a pointer to
// s.n through reflect's UnsafePointer.
func Leak(s *S) *int {
	return (*int)(reflect.ValueOf(s).Elem().Field(1).Addr().UnsafePointer())
}

// Keep writes what p points to and claims s.n unchanged.
//
// @Requires p != nil And s != nil
// @Modifies p
// @Ensures s.n' = s.n
func Keep(p *int, s *S) {
	*p = 7
} // want `vego: postcondition may not hold: s\.n' = s\.n`
