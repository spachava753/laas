// Package dynifaces holds assertions and cases of interface types (S2 of
// F34): the programs a user writes first, which verify.
package dynifaces

import (
	"errors"
	"fmt"
	"io"
)

// Shape is a sum type whose method has a contract.
type Shape interface {
	// @Ensures a >= 0
	Area() (a int)
}

// Named has a method without one.
type Named interface{ Name() string }

// Circle is a Shape and Named.
type Circle struct{ R int }

// @Ensures a = 0
func (c Circle) Area() (a int) { return 0 }

func (c Circle) Name() string { return "circle" }

// Square is a Shape only.
type Square struct{ S int }

// @Ensures a = 0
func (s Square) Area() (a int) { return 0 }

// What a value implements, asked of values converted here, in both
// orders.
//
// @Ensures ok And ~ok2
func CircleNamedSquareNot() (ok, ok2 bool) {
	var a any = Circle{R: 1}
	var b any = Square{S: 2}
	_, ok = a.(Named)
	_, ok2 = b.(Named)
	return ok, ok2
}

// @Ensures ~ok And ok2
func SquareNotCircleNamed() (ok, ok2 bool) {
	var b any = Square{S: 2}
	var a any = Circle{R: 1}
	_, ok = b.(Named)
	_, ok2 = a.(Named)
	return ok, ok2
}

// A target whose method has a contract, asked only whether it holds one.
//
// @Ensures ok And ~ok2
func ShapeOrNot() (ok, ok2 bool) {
	var a any = Circle{R: 3}
	var b any = 7
	_, ok = a.(Shape)
	_, ok2 = b.(Shape)
	return ok, ok2
}

// @Ensures True
func IsNamed(v any) (ok bool) {
	_, ok = v.(Named)
	return ok
}

// Cases of interface types, in order: Circle is a Shape before it is
// Named, and Named before it is a Shape.
//
// @Ensures v = nil -> k = 0
// @Ensures holds(v, int) -> k = 1
func Kind(v any) (k int) {
	switch v.(type) {
	case nil:
		return 0
	case int:
		return 1
	case Shape:
		return 2
	case Named:
		return 3
	case error:
		return 4
	}
	return 5
}

// @Ensures k = 2 And n = 3
func ShapeFirst() (k, n int) {
	var v any = Circle{R: 1}
	switch v.(type) {
	case Shape:
		k = 2
	case Named:
		k = 3
	}
	switch v.(type) {
	case Named:
		n = 3
	case Shape:
		n = 2
	}
	return k, n
}

// error asked of an any.
//
// @Ensures ok And ~ok2 And ok3
func ErrorsInAny() (ok, ok2, ok3 bool) {
	var a any = &CodeErr{Code: 1}
	var b any = 4
	var c any = errors.New("x")
	_, ok = a.(error)
	_, ok2 = b.(error)
	_, ok3 = c.(error)
	return ok, ok2, ok3
}

// CodeErr is an error of the project.
type CodeErr struct{ Code int }

// @Ensures True
func (e *CodeErr) Error() (s string) { return "code" }

// An interface value asserted to an interface whose methods its type has:
// a conversion that asks whether it is nil.
//
// @Requires rw != nil
// @Ensures r = rw
func AsReader(rw io.ReadWriter) (r io.Reader) {
	return rw.(io.Reader)
}

// @Ensures ok <-> ~(rw = nil)
func MaybeReader(rw io.ReadWriter) (r io.Reader, ok bool) {
	r, ok = rw.(io.Reader)
	return r, ok
}

// An error asserted to an interface (item 5).

// Timeouter has a method without a contract.
type Timeouter interface{ Timeout() bool }

// TimeoutErr is an error that times out.
type TimeoutErr struct{}

// @Ensures True
func (e *TimeoutErr) Error() (s string) { return "timeout" }

// @Ensures t
func (e *TimeoutErr) Timeout() (t bool) { return true }

// @Ensures ok And ~ok2
func TimeoutOrNot() (ok, ok2 bool) {
	var err error = &TimeoutErr{}
	made := errors.New("x")
	_, ok = err.(Timeouter)
	_, ok2 = made.(Timeouter)
	return ok, ok2
}

// @Ensures ~ok And ok2
func NotThenTimeout() (ok, ok2 bool) {
	made := errors.New("x")
	var err error = &TimeoutErr{}
	_, ok = made.(Timeouter)
	_, ok2 = err.(Timeouter)
	return ok, ok2
}

// An interface literal as the target.
//
// @Ensures ok
func TimeoutLiteral() (ok bool) {
	var err error = &TimeoutErr{}
	_, ok = err.(interface{ Timeout() bool })
	return ok
}

// The value of an error asserted to an interface holds the error.
//
// @Ensures ok -> ~(t = nil)
// @Ensures ~ok -> t = nil
func AsTimeouter(err error) (t Timeouter, ok bool) {
	t, ok = err.(Timeouter)
	return t, ok
}

// @Ensures ok
func BackToConcrete() (ok bool) {
	var err error = &TimeoutErr{}
	t, isT := err.(Timeouter)
	if !isT {
		return false
	}
	_, ok = t.(*TimeoutErr)
	return ok
}

// @Ensures k = 1 And n = 2
func SwitchOnError() (k, n int) {
	var err error = &TimeoutErr{}
	switch err.(type) {
	case nil:
		k = 0
	case Timeouter:
		k = 1
	default:
		k = 2
	}
	made := errors.New("x")
	switch made.(type) {
	case nil:
		n = 0
	case Timeouter:
		n = 1
	default:
		n = 2
	}
	return k, n
}

// @Ensures True
func TimeouterOf(err error) (t Timeouter) {
	switch e := err.(type) {
	case Timeouter:
		return e
	}
	return nil
}

// An error of any type put in an any holds a value that implements error.
//
// @Ensures ok <-> ~(err = nil)
func ErrParamInAny(err error) (ok bool) {
	var v any = err
	_, ok = v.(error)
	return ok
}

// Whether a made error wraps is decided by its call (F17 of the review of
// S2).
//
// @Ensures ~a And b And c And ~d
func MadeUnwrap() (a, b, c, d bool) {
	inner := errors.New("inner")
	_, a = inner.(interface{ Unwrap() error })
	_, b = fmt.Errorf("w: %w", inner).(interface{ Unwrap() error })
	_, c = fmt.Errorf("%w and %w", inner, inner).(interface{ Unwrap() []error })
	_, d = fmt.Errorf("x %d", 1).(interface{ Unwrap() error })
	return a, b, c, d
}
