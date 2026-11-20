package trialfaults

import "errors"

var errBad = errors.New("bad")

// unpredictable fails as its trusted contract allows, which says nothing of
// when it succeeds.
func unpredictable() error { return nil }

// A function that reports a fault of its own is not judged by the
// always-fails check until the fault is fixed: Faulty's contract would draw
// that report, and only the index is reported.
//
// @Ensures err = nil Or err = errBad
func Faulty(a []int) (n int, err error) {
	return a[3], errBad // want `index may be out of range`
}

// Without the fault, the same contract draws the report.
//
// @Ensures err = nil Or err = errBad
func Unfaulty(a []int) (n int, err error) { // want `the contract of Unfaulty may also be met by a function that always returns an error`
	return 0, errBad
}

// failsOutside has a fault of its own, and reaches a call whose failure
// nothing predicts, so it cannot promise success: it is excused.
//
// @Ensures True
func failsOutside(a []int) (n int, err error) {
	err = unpredictable()
	return a[1], err // want `index may be out of range`
}

// Excused verifies: it reaches failsOutside, which is excused, and so it
// is excused too, although failsOutside reported a fault of its own and was
// not judged for itself.
//
// @Ensures True
func Excused(a []int) (n int, err error) {
	return failsOutside(a)
}
