// Package dyneq holds == on interface values (S3 of F34): the programs a
// user writes first, which verify.
package dyneq

import "errors"

// Shape is a sum type.
type Shape interface {
	// @Ensures a >= 0
	Area() (a int)
}

// Circle is a Shape.
type Circle struct{ R int }

// @Ensures a = 0
func (c Circle) Area() (a int) { return 0 }

// Rect is a Shape.
type Rect struct{ W, H int }

// @Ensures a = 0
func (r Rect) Area() (a int) { return 0 }

// A value compared with a constant.
//
// @Ensures r <-> holds(v, int) And v.(int) = 3
func IsThree(v any) (r bool) {
	return v == 3
}

// @Ensures r <-> holds(v, string) And v.(string) = "x"
func IsX(v any) (r bool) {
	return v == "x"
}

// Values converted here, compared in both orders.
//
// @Ensures a And ~b And ~c
func Compared() (a, b, c bool) {
	x, y, z := any(3), any(3), any(4)
	w := any("3")
	return x == y, x == z, w == x
}

// @Ensures a And ~b And ~c
func ComparedSwapped() (a, b, c bool) {
	w := any("3")
	x, y, z := any(3), any(3), any(4)
	return y == x, z == x, x == w
}

// Two values of which a contract says what they hold.
//
// @Requires holds(a, int) And holds(b, int)
// @Ensures r <-> a.(int) = b.(int)
func SameInts(a, b any) (r bool) {
	return a == b
}

// nil beside a value.
//
// @Ensures a And ~b
func Nils() (a, b bool) {
	var x, y any
	z := any(1)
	return x == y, x == z
}

// A sum type compared with a value of one of its types.
//
// @Ensures r <-> holds(sh, Circle) And sh.(Circle).R = 1
func IsUnitCircle(sh Shape) (r bool) {
	return sh == Circle{R: 1}
}

// @Ensures a And ~b And ~c
func Shapes() (a, b, c bool) {
	var s, t Shape = Circle{R: 2}, Rect{W: 2, H: 2}
	return s == Circle{R: 2}, s == t, t == Circle{R: 2}
}

// @Ensures a And ~b
func ShapesSwapped() (a, b bool) {
	var t, s Shape = Rect{W: 2, H: 2}, Circle{R: 2}
	return Circle{R: 2} == s, Circle{R: 2} == t
}

// != is the negation of ==.
//
// @Ensures r <-> ~(holds(v, int) And v.(int) = 0)
func NotZero(v any) (r bool) {
	return v != 0
}

// Pointers held are equal when they are the same pointer.
//
// @Ensures a And ~b
func Pointers() (a, b bool) {
	p, q := &Circle{R: 1}, &Circle{R: 1}
	x, y, z := any(p), any(p), any(q)
	return x == y, x == z
}

// A switch on an interface value, with cases of concrete types and nil.
//
// @Ensures v = nil -> k = 0
// @Ensures holds(v, int) And v.(int) = 1 -> k = 1
// @Ensures holds(v, string) And v.(string) = "one" -> k = 2
func Name(v any) (k int) {
	switch v {
	case nil:
		return 0
	case 1:
		return 1
	case "one":
		return 2
	}
	return 3
}

// @Ensures k = 2 And n = 1
func Names() (k, n int) {
	return Name("one"), Name(1)
}

// A switch on a concrete value with a case that is an interface value.
//
// @Ensures r <-> holds(a, int) And a.(int) = n
func Matches(n int, a any) (r bool) {
	switch n {
	case a:
		return true
	}
	return false
}

// An error beside an any.
//
// @Ensures r
func ErrInAny() (r bool) {
	err := errors.New("x")
	var v any = err
	return v == err
}

// @Ensures ~r
func OtherErr() (r bool) {
	err := errors.New("x")
	var v any = 3
	return v == err
}

// == on two paths.
//
// @Ensures r
func TwoPathsEq(c bool) (r bool) {
	a := any(3)
	if c {
		return a == any(3)
	}
	return any(3) == a
}
