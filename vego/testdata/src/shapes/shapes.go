// Package shapes declares a type with an invariant that another package uses.
package shapes

// Limit bounds the sides of a Rect.
const Limit = 100

// Rect has sides that are not negative and not too long.
//
// @ Invariant 0 <= W <= Limit And 0 <= H <= Limit
type Rect struct {
	W, H int
}

// New returns a rectangle, which has to meet the invariant.
//
// @ Requires 0 <= w <= Limit And 0 <= h <= Limit
// @ Ensures fresh(result) And result.W = w And result.H = h
func New(w, h int) (result *Rect) {
	return &Rect{W: w, H: h}
}

// Area relies on the invariant for its arithmetic.
//
// @ Requires r != nil
// @ Ensures 0 <= result <= Limit * Limit
func (r *Rect) Area() (result int) {
	return r.W * r.H
}

// Unchecked returns a rectangle without establishing its invariant.
//
// @ Ensures fresh(result)
func Unchecked(w int) (result *Rect) {
	return &Rect{W: w} // want `invariant of Rect may not hold for the result: 0 <= W <= Limit`
}

// Broken has an invariant that cannot be read, which importing packages
// must not take for no invariant.
//
// @ Invariant X > // want `syntax error in Invariant annotation: expected an expression, found "end of annotation"`
type Broken struct{ X int }

// Never has invariants no value can meet. A function of another package
// that takes one must not be verified from that contradiction.
//
// @ Invariant X = 0 And X = 1 // want `the invariants of Never contradict each other, so no value of the type could exist`
type Never struct{ X int }
