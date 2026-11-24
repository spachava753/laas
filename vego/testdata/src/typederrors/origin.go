package typederrors

import (
	"errors"
	"fmt"
)

// Errors of the package's types have a known origin, typed (S4 of F33):
// they can be formatted, wrapped, searched with errors.Is, and read with
// Error.

// @Ensures err = nil <-> n >= 0
// @Ensures is(err, ErrSyntax) <-> n < 0
func Labelled(n int) (err error) {
	if err := Parse(n); err != nil {
		return fmt.Errorf("labelled: %w", err)
	}
	return nil
}

// @Ensures r <-> n < 0
func IsSyntax(n int) (r bool) {
	return errors.Is(Labelled(n), ErrSyntax)
}

// @Ensures ~r
func IsRange(n int) (r bool) {
	return errors.Is(Parse(n), ErrRange)
}

// @Ensures r <-> n < 0
func DirectIs(n int) (r bool) {
	return errors.Is(Parse(n), ErrSyntax)
}

// @Requires n < 0
// @Ensures 2 * (|s| + 4096) + 65536 <= MaxAlloc
func Text(n int) (s string) {
	return Parse(n).Error()
}

// @Ensures err = nil <-> |src| = 0
func WrapsByte(src []byte) (err error) {
	if len(src) > 0 {
		return fmt.Errorf("decode: %w", InvalidByteError(src[0]))
	}
	return nil
}

// Chained wraps an error of the package that holds a pointer.
//
// @Ensures err = nil <-> n = 0
func Chained(n int) (err error) {
	if err := Located(n); err != nil {
		return fmt.Errorf("at: %w", err)
	}
	return nil
}

// WithUnwrap has an Unwrap method, which errors.Is would run, so its
// errors have no known origin.
type WithUnwrap struct{ inner int }

// @Ensures True
func (w WithUnwrap) Error() (s string) { return "with unwrap" }

// @Ensures e = nil
func (w WithUnwrap) Unwrap() (e error) { return nil }

// @Ensures err != nil
func FormatsUnwrap() (err error) {
	var e error = WithUnwrap{}
	return fmt.Errorf("x: %w", e) // want `formatting e would run the methods of an error whose origin is not known; .*e is assigned WithUnwrap\{\} at origin.go:\d+:\d+, a value of type WithUnwrap, whose errors have no known origin: WithUnwrap has a method Unwrap, which errors.Is, errors.As, or fmt would run`
}

// @Ensures err != nil
func WrapsFloat() (err error) {
	return fmt.Errorf("x: %w", FErr(1)) // want `fmt.Errorf formats FErr\(1\), a value of type typederrors.FErr, which is an error that %w would wrap; only an error of known origin can be wrapped, and errors of this type have none: == on values of FErr is not identity`
}

// @Ensures err = nil <-> |src| = 0
// @Ensures |src| > 0 -> is(err, InvalidByteError(src[0]))
func WrapsByteIs(src []byte) (err error) {
	if len(src) > 0 {
		return fmt.Errorf("decode: %w", InvalidByteError(src[0]))
	}
	return nil
}

// hiddenCounter holds a pointer, which fmt follows for verbs that do not
// call Error, so its errors have no known origin.
type hiddenCounter struct{ c *Counter }

// @Ensures True
func (h hiddenCounter) Error() (s string) { return "hidden" }

// @Ensures err != nil
func FormatsPointerHolder() (err error) {
	var e error = hiddenCounter{}
	return fmt.Errorf("x: %w", e) // want `e is assigned hiddenCounter\{\} at origin.go:\d+:\d+, a value of type hiddenCounter, whose errors have no known origin: fmt prints what hiddenCounter holds for verbs that do not call Error, where \*typederrors.Counter is a pointer, which fmt would follow`
}
