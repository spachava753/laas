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
func New(w, h int) *Rect {
	return &Rect{W: w, H: h}
}

//@ Ensures fresh(result) And result.W = w And result.H = h

// Area relies on the invariant for its arithmetic.
//
// @ Requires r != nil
func (r *Rect) Area() int {
	return r.W * r.H
}

//@ Ensures 0 <= result <= Limit * Limit

// Unchecked returns a rectangle without establishing its invariant.
func Unchecked(w int) *Rect {
	return &Rect{W: w} // want `invariant of Rect may not hold for the result: 0 <= W <= Limit`
}

//@ Ensures fresh(result)

// Broken has an invariant that cannot be read, which importing packages
// must not take for no invariant.
//
// @ Invariant X > // want `syntax error in Invariant annotation: expected an expression, found "end of annotation"`
type Broken struct{ X int }
