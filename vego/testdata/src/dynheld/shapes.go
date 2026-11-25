// Package dynheld holds what interface values other than errors hold
// (S1 of F34): a small sum type, values out of an any, fields and
// elements of type any, and formulas that say what a value holds.
package dynheld

// Shape is a small sum type.
type Shape interface {
	// @Ensures a >= 0
	Area() (a int)
}

// Circle is a shape, measured coarsely.
type Circle struct{ R int }

// @Ensures a >= 0
func (c Circle) Area() (a int) {
	if c.R < 0 || c.R > 1000 {
		return 0
	}
	return 3 * c.R * c.R
}

// Rect is another shape.
type Rect struct{ W, H int }

// @Ensures a >= 0
func (r Rect) Area() (a int) {
	if r.W < 0 || r.W > 1000 || r.H < 0 || r.H > 1000 {
		return 0
	}
	return r.W * r.H
}

// @Ensures k = 0 <-> sh = nil
// @Ensures k = 1 <-> sh != nil And holds(sh, Circle)
// @Ensures k = 2 <-> sh != nil And holds(sh, Rect)
func Kind(sh Shape) (k int) {
	switch sh.(type) {
	case nil:
		return 0
	case Circle:
		return 1
	case Rect:
		return 2
	}
	return 3
}

// @Ensures holds(sh, Circle) -> r = sh.(Circle).R
// @Ensures ~holds(sh, Circle) -> r = 0
func Radius(sh Shape) (r int) {
	c, ok := sh.(Circle)
	if ok {
		return c.R
	}
	return 0
}

// @Requires holds(sh, Rect)
// @Ensures w = sh.(Rect).W
func Width(sh Shape) (w int) {
	return sh.(Rect).W
}

// @Requires 0 <= r <= 1000
// @Ensures sh != nil And holds(sh, Circle) And sh.(Circle).R = r
func MakeCircle(r int) (sh Shape) {
	return Circle{R: r}
}

// @Requires 0 <= w <= 1000 And 0 <= h <= 1000
// @Ensures sh != nil And holds(sh, Rect) And sh.(Rect).W = w And sh.(Rect).H = h
func MakeRect(w, h int) (sh Shape) {
	return Rect{W: w, H: h}
}

// Two shapes, made and asked in both orders.
//
// @Ensures n = 14
func TwoShapes() (n int) {
	a := MakeCircle(3)
	b := MakeRect(2, 6)
	return Radius(a) + Width(b) + Kind(b) + Kind(a) + Radius(b) + 6
}

// @Ensures n = 14
func TwoShapesSwapped() (n int) {
	b := MakeRect(2, 6)
	a := MakeCircle(3)
	return Kind(a) + Kind(b) + Width(b) + Radius(a) + 6
}

// The method of what a switch takes out is called under its own contract.
//
// @Ensures a >= 0
func AreaOf(sh Shape) (a int) {
	switch s := sh.(type) {
	case Circle:
		return s.Area()
	case Rect:
		return s.Area()
	}
	return 0
}

// A pointer in a shape, and a nil pointer in a shape that is not nil.

// Square is a shape held by pointer.
type Square struct{ S int }

// @Ensures a >= 0
func (q *Square) Area() (a int) {
	if q == nil || q.S < 0 || q.S > 1000 {
		return 0
	}
	return q.S * q.S
}

// @Ensures sh != nil And holds(sh, *Square) And sh.(*Square) = nil
func NilSquare() (sh Shape) {
	var q *Square
	return q
}

// @Ensures r
func NilSquareIsNotNil() (r bool) {
	sh := NilSquare()
	q, ok := sh.(*Square)
	return sh != nil && ok && q == nil
}
