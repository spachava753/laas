package dynifaces

import (
	"errors"
	"fmt"
	"io"
	"os"
	"strconv"
)

// What is refused or not proved (S2 of F34).

// The value of an assertion to an interface whose methods the operand's
// type lacks may be one verified code made without checking it against
// them (R2).
//
// @Ensures True
func UsesNamed(v any) (s string) {
	if n, ok := v.(Named); ok { // want `cannot verify UsesNamed: using the value of v.\(Named\) is not supported: Named has the method Name, which any does not have`
		return describe(n)
	}
	return ""
}

func describe(n Named) string { return n.Name() }

// @Ensures True
func UsesNamedCase(v any) (s string) {
	switch n := v.(type) {
	case Named: // want `cannot verify UsesNamedCase: using the variable of the case Named of the type switch is not supported: Named has the method Name, which any does not have`
		return describe(n)
	}
	return ""
}

// Picky's Error asks something of its receiver, which nothing checked
// where it was converted to an any (F1 of the design review).
type Picky struct{ n int }

// @Requires p.n > 0
// @Ensures True
func (p Picky) Error() (s string) { return strconv.Itoa(10 / p.n) }

// @Ensures True
func ConvertedThroughAny() (e error) {
	var v any = Picky{}
	e, _ = v.(error) // want `cannot verify ConvertedThroughAny: using the value of v.\(error\) is not supported: error has the method Error, which any does not have`
	return e
}

// A method of the same name from another declaration, without a contract
// (F2 of the design review).
type Areaer interface{ Area() int }

// @Requires sh != nil
// @Ensures True
func ToAreaer(sh Shape) (n int) {
	if a, ok := sh.(Areaer); ok { // want `cannot verify ToAreaer: asserting sh, a Shape, to Areaer is not supported: Areaer.Area has no contract`
		return measure(a)
	}
	return 0
}

func measure(a Areaer) int { return a.Area() }

// A target whose method has a contract cannot be taken out of an error
// (AC), but can be asked about.
type Coder interface {
	// @Ensures c >= 0
	Code() (c int)
}

// @Ensures c >= 0
func CodeOf(err error) (c int) {
	if k, ok := err.(Coder); ok { // want `cannot verify CodeOf: using the value of err.\(Coder\) is not supported: the method Code of Coder has a contract, and nothing claims that what the error holds meets it`
		return k.Code()
	}
	return 0
}

// @Ensures True
func IsCoder(err error) (ok bool) {
	_, ok = err.(Coder)
	return ok
}

// A target with states cannot be taken out of an error.
//
// @Ensures True
func CloserOf(err error) (c io.Closer) {
	c, _ = err.(io.Closer) // want `cannot verify CloserOf: using the value of err.\(io.Closer\) is not supported: io.Closer has methods whose contracts speak of its states`
	return c
}

// @Ensures True
func IsCloser(err error) (ok bool) {
	_, ok = err.(io.Closer)
	return ok
}

// The one-result form panics on nil.
//
// @Ensures True
func MustReader(rw io.ReadWriter) (r io.Reader) {
	return rw.(io.Reader) // want `the type assertion rw.\(io.Reader\) may panic: rw may not hold a value that implements io.Reader`
}

// An interface declared in a function has no name.
//
// @Ensures True
func LocalIface(v any) (ok bool) {
	type L interface{ M() }
	_, ok = v.(L) // want `cannot verify LocalIface: asserting an interface value to L is not supported: it is declared inside a function`
	return ok
}

// Two types declared in a function have no tags, so nothing is known of
// what they implement.

// Impl has M.
type Impl struct{}

func (Impl) M() {}

// Mer has M.
type Mer interface{ M() }

// @Ensures ok1 And ok2
func TwoLocals() (ok1, ok2 bool) {
	type L1 struct{ Impl }
	type L2 struct{ n int }
	var a any = L1{}
	var b any = L2{}
	_, ok1 = a.(Mer)
	_, ok2 = b.(Mer)
	return ok1, ok2 // want `postcondition may not hold: ok1` `postcondition may not hold: ok2`
}

// Claims that say too much.
//
// @Ensures ok
func SquareNamed() (ok bool) {
	var a any = Square{S: 1}
	_, ok = a.(Named)
	return ok // want `postcondition may not hold: ok`
}

// @Ensures ~ok
func CircleNotNamed() (ok bool) {
	var a any = Circle{R: 1}
	_, ok = a.(Named)
	return ok // want `postcondition may not hold: ~ok`
}

// @Ensures ok
func ClaimsNamed(v any) (ok bool) {
	_, ok = v.(Named)
	return ok // want `postcondition may not hold: ok`
}

// fmt.Errorf with %w makes an error that unwraps.
//
// @Ensures ~ok
func WrappedUnwraps() (ok bool) {
	err := fmt.Errorf("x: %w", errors.New("y"))
	_, ok = err.(interface{ Unwrap() error })
	return ok // want `postcondition may not hold: ~ok`
}

// A case that comes first is taken first.
//
// @Ensures k = 3
func NamedAfterShape() (k int) {
	var v any = Circle{R: 1}
	switch v.(type) {
	case Shape:
		k = 2
	case Named:
		k = 3
	}
	return k // want `postcondition may not hold: k = 3`
}

// What an error asserted to an interface holds is the error's.
//
// @Ensures ~ok
func BackIsNot() (ok bool) {
	var err error = &TimeoutErr{}
	t, isT := err.(Timeouter)
	if !isT {
		return false
	}
	_, ok = t.(*TimeoutErr)
	return ok // want `postcondition may not hold: ~ok`
}

// An interface value with a method Error asserted to error is not
// followed as an error.
//
// @Ensures True
func ErrorOfCoded(v interface{ Error() string }) (e error) {
	e, _ = v.(error) // want `cannot verify ErrorOfCoded: using the value of v.\(error\) is not supported: an error made from a value of interface\{Error\(\) string\} is not followed as an error`
	return e
}

// The states of a file taken out through an io.Reader are those of the
// closer it came from (F11 of the design review, through an assertion to
// an interface without states).
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func TwiceThroughReader(c io.ReadCloser) (err error) {
	if r, ok := c.(io.Reader); ok {
		if f, ok := r.(*os.File); ok && f != nil {
			f.Close() // want `Close may modify f, which TwiceThroughReader may not modify`
		}
	}
	return c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}
