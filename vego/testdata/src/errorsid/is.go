package errorsid

import (
	"errors"
	"fmt"
	"strconv"
)

// Sum passes on the error of Head wrapped with %w, so errors.Is still
// finds ErrEmpty in it.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures is(err, ErrEmpty) <-> |A| = 0
func Sum(A []int) (s int, err error) {
	h, err := Head(A)
	if err != nil {
		return 0, fmt.Errorf("sum: %w", err)
	}
	return h, nil
}

// SumWrongly formats the error with %v, which does not wrap it.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures is(err, ErrEmpty) <-> |A| = 0
func SumWrongly(A []int) (s int, err error) {
	h, err := Head(A)
	if err != nil {
		return 0, fmt.Errorf("sum: %v", err) // want `vego: postcondition may not hold: is\(err, ErrEmpty\) <-> \|A\| = 0`
	}
	return h, nil
}

// IsEmpty asks errors.Is about an error of known origin.
//
// @Ensures empty <-> |A| = 0
func IsEmpty(A []int) (empty bool) {
	_, err := Sum(A)
	return errors.Is(err, ErrEmpty)
}

// IsFull asks about another sentinel. The contract of Sum says nothing
// about it, so the answer is not known.
//
// @Ensures full = False
func IsFull(A []int) (full bool) {
	_, err := Sum(A)
	return errors.Is(err, ErrFull) // want `vego: postcondition may not hold: full = False`
}

// ParseIs asks errors.Is about the error of a trusted call, whose methods
// nobody has seen.
//
// @Ensures True
func ParseIs(s string) (bad bool) {
	_, err := strconv.Atoi(s)
	return errors.Is(err, strconv.ErrSyntax) // want `vego: cannot verify ParseIs: errors.Is would run the Is and Unwrap methods of err, an error whose origin is not known`
}

// Holds asks errors.Is about a sentinel and a target of which nothing is
// known; errors.Is runs no method of the target.
//
// @Ensures b <-> e = ErrEmpty
func Holds(e error) (b bool) {
	return errors.Is(ErrEmpty, e)
}

// WrapsNil wraps an error that is nil, which wraps nothing.
//
// @Ensures err = nil <-> ~fail
// @Ensures ~is(err, ErrEmpty)
func WrapsNil(fail bool) (err error) {
	var none error
	if fail {
		return fmt.Errorf("none: %w", none)
	}
	return nil
}

// Several %w, a format that is not a constant, explicit argument indexes,
// and widths taken from operands still make an error of known origin, but
// what errors.Is finds in it is not known either way.

// @Ensures err != nil -> is(err, ErrEmpty)
// @Ensures err = nil <-> ~fail
func TwoWraps(fail bool) (err error) {
	if fail {
		return fmt.Errorf("%w; %w", ErrEmpty, ErrFull) // want `vego: postcondition may not hold: err != nil -> is\(err, ErrEmpty\)`
	}
	return nil
}

// @Ensures err != nil -> ~is(err, ErrEmpty)
// @Ensures err = nil <-> ~fail
func TwoWrapsNot(fail bool) (err error) {
	if fail {
		return fmt.Errorf("%w; %w", ErrEmpty, ErrFull) // want `vego: postcondition may not hold: err != nil -> ~is\(err, ErrEmpty\)`
	}
	return nil
}

// @Ensures err = nil <-> ~fail
func Unread(fail bool, format string, n int) (err error) {
	if !fail {
		return nil
	}
	switch n {
	case 0:
		return fmt.Errorf(format, ErrEmpty)
	case 1:
		return fmt.Errorf("%[1]v: %[1]w", ErrEmpty)
	}
	return fmt.Errorf("%*d: %w", 3, n, ErrEmpty)
}

// @Ensures err != nil -> is(err, ErrEmpty)
// @Ensures err = nil <-> ~fail
func UnreadIs(fail bool, format string) (err error) {
	if fail {
		return fmt.Errorf(format, ErrEmpty) // want `vego: postcondition may not hold: err != nil -> is\(err, ErrEmpty\)`
	}
	return nil
}

// Sentinels have trees too.

var (
	ErrWrapped = fmt.Errorf("wrapped: %w", ErrEmpty)
	oddFormat  = "odd: %w"
	ErrOdd     = fmt.Errorf(oddFormat, ErrEmpty)
)

// @Ensures empty And ~full
func Wrapped() (empty, full bool) {
	return errors.Is(ErrWrapped, ErrEmpty), errors.Is(ErrWrapped, ErrFull)
}

// What ErrOdd wraps is not known, since its format is not a constant.

// @Ensures b
func OddIs() (b bool) {
	return errors.Is(ErrOdd, ErrEmpty) // want `vego: postcondition may not hold: b`
}

// @Ensures ~b
func OddIsNot() (b bool) {
	return errors.Is(ErrOdd, ErrEmpty) // want `vego: postcondition may not hold: ~b`
}

// @Ensures True
func Deferred() {
	defer errors.Is(ErrEmpty, ErrFull) // want `vego: cannot verify Deferred: deferring errors.Is is not supported`
}

// WrappedFull claims errors.Is finds a sentinel that ErrWrapped does not
// wrap.
//
// @Ensures b
func WrappedFull() (b bool) {
	return errors.Is(ErrWrapped, ErrFull) // want `vego: postcondition may not hold: b`
}
