// Package typederrorsclient reads the contracts of typederrors, whose
// formulas name its types and constants, from another package (S2 of F33).
package typederrorsclient

import (
	"errors"
	"fmt"

	"typederrors"
)

// @Ensures r <-> n < 0
func Failed(n int) (r bool) {
	return typederrors.Parse(n) == typederrors.ErrSyntax
}

// @Ensures ~r
func NotRange(n int) (r bool) {
	return typederrors.Parse(n) == typederrors.ErrRange
}

// @Ensures err = nil <-> n >= 0
// @Ensures n < 0 -> err = typederrors.ErrSyntax
func Forward(n int) (err error) {
	return typederrors.Parse(n)
}

// @Ensures err = nil <-> n = 0
// @Ensures n != 0 -> holds(err, *typederrors.PE) And err.(*typederrors.PE).Line = n
func ForwardLocated(n int) (err error) {
	return typederrors.Located(n)
}

// @Ensures err = nil <-> |src| = 0
// @Ensures |src| > 0 -> err = typederrors.InvalidByteError(src[0])
func ForwardByte(src []byte) (err error) {
	return typederrors.FirstByte(src)
}

// @Ensures err = nil <-> n >= 0
// @Ensures n < 0 -> err = typederrors.ErrRange
func WrongForward(n int) (err error) {
	return typederrors.Parse(n) // want `postcondition may not hold: n < 0 -> err = typederrors.ErrRange`
}

// find stands for a trusted function that returns a typed error; its
// entry names the type by its path.
func find(n int) error {
	if n < 0 {
		return &typederrors.PE{Line: n}
	}
	return nil
}

// @Ensures n < 0 -> line = n
func Found(n int) (line int) {
	err := find(n)
	if err == nil {
		return n
	}
	return n
}

// @Ensures err = nil <-> n >= 0
// @Ensures n < 0 -> err.(*typederrors.PE).Line = n
func ForwardFound(n int) (err error) {
	return find(n)
}

// @Ensures err = nil <-> n >= 0
// @Ensures is(err, typederrors.ErrSyntax) <-> n < 0
func Wraps(n int) (err error) {
	if err := typederrors.Parse(n); err != nil {
		return fmt.Errorf("client: %w", err)
	}
	return nil
}

// wrapped stands for a trusted function that returns a typederrors.Wrap,
// which embeds a *PE; its entry says what the error holds.
func wrapped() (err error) { return typederrors.Wrap{PE: &typederrors.PE{Line: 1}} }

// AsUnnamed asks errors.As for an unnamed struct that a Wrap is assignable
// to, which it finds (F3 of the design review).
//
// @Ensures r
func AsUnnamed() (r bool) {
	var v struct{ *typederrors.PE }
	return errors.As(wrapped(), &v)
}

// AsTypeUnnamed asks errors.AsType for the same, which tests identity and
// finds nothing.
//
// @Ensures ~r
func AsTypeUnnamed() (r bool) {
	_, r = errors.AsType[struct{ *typederrors.PE }](wrapped())
	return r
}
