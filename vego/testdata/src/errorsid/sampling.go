// Package errorsid holds programs about which error an error is.
package errorsid

import (
	"errors"
	"strconv"
)

var ErrNegative = errors.New("negative")

// The search for an input on which a contract forces success can give two
// errors different values, and the same value.

// @Requires e1 != nil And e2 != nil And e1 != e2
// @Ensures err = nil
func TwoDistinct(e1, e2 error) (err error) {
	return nil
}

// @Requires e1 != nil And e1 = e2
// @Ensures err = nil
func TwoEqual(e1, e2 error) (err error) {
	return nil
}

// @Requires e1 != nil And e2 != nil And e3 != nil And e1 != e2 And e2 != e3 And e1 != e3
// @Ensures err = nil
func ThreeDistinct(e1, e2, e3 error) (err error) {
	return nil
}

// A path to a call that may fail unpredictably is reached by an input with
// two different errors, so the function is excused.

// @Requires e1 != nil And e2 != nil And e1 != e2
// @Ensures err = nil -> n >= 0
func ParseDistinct(e1, e2 error, s string) (n int, err error) {
	n, err = strconv.Atoi(s)
	if err != nil {
		return 0, err
	}
	if n < 0 {
		return 0, ErrNegative
	}
	return n, nil
}

// Errors that differ do not make a weak contract strong.

// @Requires e1 != e2
// @Ensures err = nil -> True
func WeakDistinct(e1, e2 error) (err error) { // want `the contract of WeakDistinct may also be met by a function that always returns an error`
	return nil
}

// A sample error may also be a sentinel the contract names.

// @Requires e = ErrNegative
// @Ensures err = nil
func GivenSentinel(e error) (err error) {
	return nil
}

// @Requires e = ErrNegative
// @Ensures err = nil -> n >= 0
func ParseGiven(e error, s string) (n int, err error) {
	n, err = strconv.Atoi(s)
	if err != nil {
		return 0, err
	}
	if n < 0 {
		return 0, e
	}
	return n, nil
}
