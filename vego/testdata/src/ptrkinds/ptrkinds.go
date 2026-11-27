// Package ptrkinds passes pointers to numbers through contracts, fields,
// and loops, where whether a pointer points into an array is known from a
// formula or a store and not from the expression that made it (F11 of the
// review of step 1 of F42).
package ptrkinds

// S holds numbers.
type S struct{ A, B int }

// Id returns the pointer it is given.
//
// @Ensures r = p
func Id(p *int) (r *int) {
	return p
}

// ThroughId writes s.A through what Id returns.
//
// @Requires s != nil
// @Modifies s
// @Ensures s.A' = 5 And s.B' = s.B
func ThroughId(s *S) {
	q := Id(&s.A)
	*q = 5
}

// H holds a pointer.
type H struct{ P *int }

// ThroughField stores &s.A in a field and writes through it.
//
// @Requires s != nil And h != nil
// @Modifies s, h
// @Ensures s.A' = 6 And s.B' = s.B
func ThroughField(s *S, h *H) {
	h.P = &s.A
	*h.P = 6
}

// Thirty writes through one pointer of unknown kind.
//
// @Requires p != nil
// @Modifies p
// @Ensures *p' = 30
func Thirty(p *int) {
	*p = 1
	*p = 2
	*p = 3
	*p = 4
	*p = 5
	*p = 6
	*p = 7
	*p = 8
	*p = 9
	*p = 10
	*p = 11
	*p = 12
	*p = 13
	*p = 14
	*p = 15
	*p = 16
	*p = 17
	*p = 18
	*p = 19
	*p = 20
	*p = 21
	*p = 22
	*p = 23
	*p = 24
	*p = 25
	*p = 26
	*p = 27
	*p = 28
	*p = 29
	*p = 30
}

// Count adds n to what p points to, one at a time.
//
// @Requires p != nil And 0 <= n < 100 And 0 <= *p < 100
// @Modifies p
// @Ensures *p' = *p + n
func Count(p *int, n int) {
	// @Invariant 0 <= i <= n And *p = old(*p) + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		*p = *p + 1
	}
}

// CountField counts into a field and keeps the other.
//
// @Requires s != nil And 0 <= s.A < 100
// @Modifies s
// @Ensures s.A' = s.A + 3 And s.B' = s.B
func CountField(s *S) {
	Count(&s.A, 3)
}

// CountElem counts into an element and keeps the next one.
//
// @Requires |xs| > 1 And 0 <= xs[0] < 100
// @Modifies xs
// @Ensures xs'[0] = xs[0] + 3 And xs'[1] = xs[1]
func CountElem(xs []int) {
	Count(&xs[0], 3)
}

// CountThroughField hands Count a pointer read from a field.
//
// @Requires s != nil And h != nil And 0 <= s.A < 100
// @Modifies s, h
// @Ensures s.A' = s.A + 3
func CountThroughField(s *S, h *H) {
	h.P = &s.A
	Count(h.P, 3)
}

// LocalPointer keeps the pointer in a local variable, whose #arr is the
// literal false.
//
// @Requires s != nil
// @Modifies s
// @Ensures s.A' = 7
func LocalPointer(s *S) {
	q := &s.A
	*q = 7
}
