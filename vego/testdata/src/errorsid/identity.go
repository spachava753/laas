package errorsid

import (
	"errors"
	"fmt"
	"io"
	"os"
	"strconv"
)

var (
	ErrEmpty = errors.New("empty")
	ErrFull  = errors.New("full")
)

// Head says which error it returns, and when.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures err = ErrEmpty <-> |A| = 0
// @Ensures err = nil -> first = A[0]
func Head(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

// HeadNew returns a new error, which is not ErrEmpty.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures err = ErrEmpty <-> |A| = 0
func HeadNew(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, errors.New("empty") // want `vego: postcondition may not hold: err = ErrEmpty <-> \|A\| = 0`
	}
	return A[0], nil
}

// Two sentinels are different errors.
//
// @Ensures err = ErrEmpty -> err != ErrFull
// @Ensures err = nil <-> n > 0
func Check(n int) (err error) {
	if n > 0 {
		return nil
	}
	return ErrEmpty
}

// HeadOrZero compares the error of a verified call with a sentinel.
//
// @Ensures v = 0 <-> (|A| = 0 Or A[0] = 0)
func HeadOrZero(A []int) (v int) {
	first, err := Head(A)
	if err == ErrEmpty {
		return 0
	}
	return first
}

// HeadOrWrong claims a comparison is never true.
//
// @Ensures v = 1
func HeadOrWrong(A []int) (v int) {
	_, err := Head(A)
	if err == ErrEmpty {
		return 0 // want `vego: postcondition may not hold: v = 1`
	}
	return 1
}

// ErrBadNumber is returned for a string that is not a number.
var ErrBadNumber = errors.New("bad number")

// Parse compares the error of a trusted call, whose origin is not known,
// with a sentinel of another package, which is a pointer, so the
// comparison cannot panic.
//
// @Ensures err = nil -> n >= 0
func Parse(s string) (n int, err error) {
	n, err = strconv.Atoi(s)
	if err == strconv.ErrSyntax {
		return 0, ErrBadNumber
	}
	if err != nil {
		return 0, err
	}
	if n < 0 {
		return 0, ErrNegative
	}
	return n, nil
}

// End returns a sentinel of another package, which its contract names.
//
// @Ensures err = io.EOF <-> |A| = 0
// @Ensures err = nil <-> |A| > 0
func End(A []int) (err error) {
	if len(A) == 0 {
		return io.EOF
	}
	return nil
}

// EndWrongly claims a sentinel of another package is one of this package.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures err != ErrEmpty
func EndWrongly(A []int) (err error) {
	if len(A) == 0 {
		return ErrEmpty // want `vego: postcondition may not hold: err != ErrEmpty`
	}
	return nil
}

// IsEnd compares with a sentinel of another package in a switch.
//
// @Ensures end <-> e = io.EOF
func IsEnd(e error) (end bool) {
	switch e {
	case io.EOF:
		return true
	}
	return false
}

// NotNew compares an unknown error with a new one. The new one is a
// pointer, so the comparison cannot panic. That they differ is not known:
// a new error is known to differ only from sentinels and from other new
// errors of the function.
//
// @Ensures True
func NotNew(e error) (same bool) {
	return e == errors.New("new")
}

// Unrelated compares two errors of which nothing is known.
//
// @Ensures True
func Unrelated(e, f error) (same bool) {
	return e != f // want `vego: cannot verify Unrelated: comparing two errors can panic when both hold the same uncomparable type`
}

// NotExist reads an error variable of another package that holds another
// variable, which is not known to be a sentinel.
//
// @Ensures True
func NotExist() (err error) {
	return os.ErrNotExist // want `vego: cannot verify NotExist: os.ErrNotExist is a variable of package os that is not known to hold the error it was declared with`
}

// NotExistNamed names it in a contract.
//
// @Ensures err != os.ErrNotExist // want `vego: in Ensures annotation: os.ErrNotExist is a variable of package os that is not known to hold the error it was declared with`
func NotExistNamed() (err error) {
	return nil
}

// Pair has an invariant that would name an error variable.
//
// @Invariant Err != ErrEmpty // want `an invariant cannot name the error variable ErrEmpty yet`
type Pair struct {
	Err error
}

// Same promises what errors.Is reports when one of the two is nil.
//
// @Ensures is(err, e) <-> is(e, e)
func Same(e error) (err error) {
	return e
}

// NilIsNil claims errors.Is reports false for two nil errors.
//
// @Ensures err = nil <-> ~fail
// @Ensures is(err, nil) -> err != nil
func NilIsNil(fail bool) (err error) {
	if fail {
		return ErrFull
	}
	return nil // want `vego: postcondition may not hold: is\(err, nil\) -> err != nil`
}

// Formats wraps a sentinel of another package made by errors.New, which
// has a known origin.
//
// @Ensures err = nil <-> fine
func Formats(fine bool) (err error) {
	if fine {
		return nil
	}
	return fmt.Errorf("read: %w", io.EOF)
}

// NilIsFull claims errors.Is reports true for nil and a sentinel.
//
// @Ensures err = nil <-> ok
// @Ensures err = nil -> is(err, ErrFull)
func NilIsFull(ok bool) (err error) {
	if ok {
		return nil // want `vego: postcondition may not hold: err = nil -> is\(err, ErrFull\)`
	}
	return ErrFull
}

// FullIsNil claims errors.Is reports true for a sentinel and nil.
//
// @Ensures err = nil <-> ok
// @Ensures err != nil -> is(err, nil)
func FullIsNil(ok bool) (err error) {
	if ok {
		return nil
	}
	return ErrFull // want `vego: postcondition may not hold: err != nil -> is\(err, nil\)`
}
