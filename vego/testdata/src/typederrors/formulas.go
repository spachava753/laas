package typederrors

import (
	"errors"
	"fmt"
)

// Formulas that say which error a function returns, when it is a value of
// one of the package's types (S2 of F33).

// InvalidByteError is a named byte error, as hex's.
type InvalidByteError byte

// @Ensures True
func (e InvalidByteError) Error() (s string) { return "invalid byte" }

// ErrVar is an error variable initialised with a constant of a type, which
// holds the error that holds the constant (F12 of the design review).
var ErrVar error = Error(2)

// @Ensures err = nil <-> n >= 0
// @Ensures n < 0 -> err = ErrSyntax
func Parse(n int) (err error) {
	if n < 0 {
		return ErrSyntax
	}
	return nil
}

// @Ensures r <-> n < 0
func ParseFailed(n int) (r bool) {
	return Parse(n) == ErrSyntax
}

// CallerDiffers relies on what the contract of Parse names holding 2,
// which the formula's own facts state.
//
// @Ensures ~r
func CallerDiffers(n int) (r bool) {
	return Parse(n) == ErrRange
}

// @Ensures err = nil <-> |src| = 0
// @Ensures |src| > 0 -> err = InvalidByteError(src[0])
func FirstByte(src []byte) (err error) {
	if len(src) > 0 {
		return InvalidByteError(src[0])
	}
	return nil
}

// @Ensures err = nil <-> |src| = 0
// @Ensures |src| > 0 -> (Exists k in [0, |src|) : err = InvalidByteError(src[k]))
func SomeByte(src []byte) (err error) {
	if len(src) > 0 {
		return InvalidByteError(src[len(src)-1])
	}
	return nil
}

// SomeByteNotSyntax relies on what an error of a value a quantifier binds
// holds, which one fact states for every value of the type.
//
// @Ensures r
func SomeByteNotSyntax(src []byte) (r bool) {
	return SomeByte(src) != ErrSyntax
}

// @Ensures err = nil <-> n = 0
// @Ensures n != 0 -> holds(err, *PE) And err.(*PE).Line = n
func Located(n int) (err error) {
	if n != 0 {
		return &PE{Line: n}
	}
	return nil
}

// @Ensures ~holds(err, *PE)
func NotLocated() (err error) { // want `the contract of NotLocated may also be met by a function that always returns an error`
	return Located(0)
}

// @Ensures err = nil <-> s = ""
// @Ensures s != "" -> err = SErr(s)
func Named(s string) (err error) {
	if s != "" {
		return SErr(s)
	}
	return nil
}

// @Ensures r
func VariableHolds() (r bool) {
	var e error = ErrSyntax
	return e == ErrVar
}

// @Ensures err = ErrVar
func ReturnsVariable() (err error) { // want `the contract of ReturnsVariable may also be met by a function that always returns an error`
	return ErrSyntax
}

// @Ensures is(err, ErrSyntax) <-> n < 0
func Wrapped(n int) (err error) {
	if n < 0 {
		return fmt.Errorf("wrapped: %w", errors.New("x")) // want `postcondition may not hold: is\(err, ErrSyntax\) <-> n < 0`
	}
	return nil
}

// @Requires holds(in, Error)
// @Ensures r <-> in.(Error) = 2
func ReadsHeld(in error) (r bool) {
	return in == ErrSyntax
}

// @Requires in = ErrSyntax Or in = ErrRange
// @Ensures err = nil <-> in = ErrRange
func PassRange(in error) (err error) {
	if in == ErrRange {
		return nil
	}
	return in
}

// @Ensures err != ErrSyntax
func NotSyntax() (err error) { // want `the contract of NotSyntax may also be met by a function that always returns an error`
	return ErrRange
}

// Label is a second string error type.
type Label string

// @Ensures True
func (e Label) Error() (s string) { return string(e) }

// LabelIsNotNamed returns an error of another string type, which a formula
// tells apart by what it holds: its type.
//
// @Ensures err != SErr(s)
func LabelIsNotNamed(s string) (err error) { // want `the contract of LabelIsNotNamed may also be met by a function that always returns an error`
	return Label(s)
}
