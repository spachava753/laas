// Package boxloops writes through pointers to numbers in loops beside a
// struct the pointer may point into. Imprecise and ImpreciseRight write
// through a variable the loop assigns, whose layer takes the frame for
// targets, so the cell of the box is kept in each region unless the
// pointer points into it (F16 of the review of step 1 of F42).
package boxloops

// S holds numbers.
type S struct{ A, B int }

// CountWrong adds n to what p points to and claims it unchanged: false
// for n > 0.
//
// @Requires p != nil And 0 < n < 100 And 0 <= *p < 100
// @Modifies p
// @Ensures *p' = *p
func CountWrong(p *int, n int) {
	// @Invariant 0 <= i <= n And *p = old(*p) + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		*p = *p + 1
	}
} // want `vego: postcondition may not hold: \*p' = \*p`

// KeepB writes through p in a loop beside s, and claims s.A unchanged:
// false when p is &s.A.
//
// @Requires p != nil And s != nil And 0 < n < 100
// @Modifies p, s.B
// @Ensures s.A' = s.A
func KeepB(p *int, s *S, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		*p = i
		s.B = i
	}
} // want `vego: postcondition may not hold: s\.A' = s\.A`

// @Requires p != nil And *p < 1000000
// @Modifies p
// @Ensures *p' = *p + 1
func inc(p *int) {
	*p = *p + 1
}

// KeepCall calls inc(p) in a loop beside s, and claims s.A unchanged:
// false when p is &s.A.
//
// @Requires p != nil And s != nil And 0 < n < 100 And 0 <= *p < 100
// @Modifies p, s.B
// @Ensures s.A' = s.A
func KeepCall(p *int, s *S, n int) {
	// @Invariant 0 <= i <= n And *p = old(*p) + i
	// @Variant n - i
	for i := 0; i < n; i++ { // want `vego: loop invariant may not be preserved: \*p = old\(\*p\) \+ i`
		inc(p)
		s.B = i
	}
} // want `vego: postcondition may not hold: s\.A' = s\.A`

// CountCall calls inc(p) n times and claims *p unchanged: false.
//
// @Requires p != nil And 0 < n < 100 And 0 <= *p < 100
// @Modifies p
// @Ensures *p' = *p
func CountCall(p *int, n int) {
	// @Invariant 0 <= i <= n And *p = old(*p) + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		inc(p)
	}
} // want `vego: postcondition may not hold: \*p' = \*p`

// CountCallRight is true.
//
// @Requires p != nil And 0 < n < 100 And 0 <= *p < 100
// @Modifies p
// @Ensures *p' = *p + n
func CountCallRight(p *int, n int) {
	// @Invariant 0 <= i <= n And *p = old(*p) + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		inc(p)
	}
}

// Imprecise writes through q, which the loop assigns, so the loop's layer
// has the frame (p, s.B) for targets; it claims s.A unchanged: false when p
// is &s.A.
//
// @Requires p != nil And s != nil And 0 < n < 100
// @Modifies p, s.B
// @Ensures s.A' = s.A
func Imprecise(p *int, s *S, n int) {
	q := p
	// @Invariant 0 <= i <= n And q = p
	// @Variant n - i
	for i := 0; i < n; i++ {
		*q = i
		q = p
		s.B = i
	}
} // want `vego: postcondition may not hold: s\.A' = s\.A`

// ImpreciseRight is true: s.A is no target when p is apart from s.
//
// @Requires p != nil And s != nil And 0 < n < 100 And apart(p, s)
// @Modifies p, s.B
// @Ensures s.A' = s.A
func ImpreciseRight(p *int, s *S, n int) {
	q := p
	// @Invariant 0 <= i <= n And q = p
	// @Variant n - i
	for i := 0; i < n; i++ {
		*q = i
		q = p
		s.B = i
	}
}
