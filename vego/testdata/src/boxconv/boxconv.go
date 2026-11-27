// Package boxconv converts pointers to elements and fields of a named number
// type to an interface whose method writes behind its receiver: the box
// they point to is one position, and no fact of byte layout holds of it
// (F13 of the review of step 1 of F42).
package boxconv

// Hits counts.
type Hits int

// Reset sets h to zero.
//
// @Requires h != nil
// @Modifies h
// @Ensures *h' = 0
func (h *Hits) Reset() {
	*h = 0
}

// Resetter resets what it holds.
type Resetter interface {
	// @Receiver r
	// @Modifies r
	// @Ensures True
	Reset()
}

// ConvertElem converts a pointer to an element and calls through it, then
// claims False.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures False
func ConvertElem(xs []Hits) {
	var r Resetter = &xs[0]
	r.Reset()
	_ = xs[0]
} // want `vego: postcondition may not hold: False`

// ConvertElemValue claims the element is 42 after Reset: false.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0] = 42
func ConvertElemValue(xs []Hits) {
	var r Resetter = &xs[0]
	r.Reset()
} // want `vego: postcondition may not hold: xs'\[0\] = 42`

// ConvertField does the same with a field.
//
// @Requires s != nil
// @Modifies s
// @Ensures False
func ConvertField(s *S) {
	var r Resetter = &s.H
	r.Reset()
	_ = s.H
} // want `vego: postcondition may not hold: False`

// S holds hits.
type S struct{ H Hits }

// TwoElems converts a pointer to xs[0], calls through it, then reads
// through a pointer to xs[1], and claims False.
//
// @Requires |xs| > 1
// @Modifies xs
// @Ensures False
func TwoElems(xs []Hits) {
	p, q := &xs[0], &xs[1]
	var r Resetter = p
	r.Reset()
	_ = *q
} // want `vego: postcondition may not hold: False`

// TwoConverted converts pointers to xs[0] and xs[1], calls through the
// first, and claims False.
//
// @Requires |xs| > 1
// @Modifies xs
// @Ensures False
func TwoConverted(xs []Hits) {
	var r0 Resetter = &xs[0]
	var r1 Resetter = &xs[1]
	r0.Reset()
	r1.Reset()
	_ = xs[0] + xs[1] // want `vego: addition may overflow boxconv\.Hits`
} // want `vego: postcondition may not hold: False`
