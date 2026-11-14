// Package wrapped holds package-level errors that wrap other errors. Such
// an error is not nil whatever it wraps, but its origin is known only if
// nothing went into it that brings code of its own: with %w the wrapped
// error stays inside, where Unwrap finds it.
package wrapped

import (
	"errors"
	"fmt"
	"io"

	"lib"
)

var (
	errBase    = errors.New("base")
	errOver    = fmt.Errorf("over: %w", errBase)
	errCounted = fmt.Errorf("%d over: %w", 3, errOver)
	errForeign = fmt.Errorf("foreign: %w", io.EOF)
	errOnTop   = fmt.Errorf("on top: %w", errForeign)
	errNumbers = fmt.Errorf("numbers: %v", [][]int{{1}, {2}})
	errNested  = fmt.Errorf("nested: %v", lib.Nest(nil))
)

func tell(e error) {}

// TellsOwn passes errors into which only errors of this package went.
func TellsOwn() {
	tell(errBase)
	tell(errOver)
	tell(errCounted)
}

//@ Ensures True

// TellsForeign passes one that holds an error of another package.
func TellsForeign() {
	tell(errForeign) // want `cannot verify TellsForeign: errForeign is passed to tell, which is trusted, and is an error whose origin is not known`
}

//@ Ensures True

// TellsOnTop passes one that holds it one step further in.
func TellsOnTop() {
	tell(errOnTop) // want `cannot verify TellsOnTop: errOnTop is passed to tell, which is trusted, and is an error whose origin is not known`
}

//@ Ensures True

// FormatsForeign wraps it again, which would run its methods.
func FormatsForeign(fine bool) error {
	if fine {
		return nil
	}
	return fmt.Errorf("again: %w", errForeign) // want `cannot verify FormatsForeign: formatting errForeign would run the methods of an error whose origin is not known`
}

//@ Ensures result = nil <-> fine

// FormatsOwn wraps one of this package.
func FormatsOwn(fine bool) error {
	if fine {
		return nil
	}
	return fmt.Errorf("again: %w", errCounted)
}

//@ Ensures result = nil <-> fine

// ReturnsForeign only hands it on. It is not nil, whatever it holds.
func ReturnsForeign(fine bool) error {
	if fine {
		return nil
	}
	return errForeign
}

//@ Ensures result = nil <-> fine

// TellsNumbers passes an error into which slices of slices of numbers went.
func TellsNumbers() {
	tell(errNumbers)
}

//@ Ensures True

// TellsNested passes one made from a slice type that is its own element
// type, which holds nothing plain however far it is followed.
func TellsNested() {
	tell(errNested) // want `cannot verify TellsNested: errNested is passed to tell, which is trusted, and is an error whose origin is not known`
}

//@ Ensures True

// FormatsNested formats such a value in verified code.
func FormatsNested(fine bool) error {
	if fine {
		return nil
	}
	return fmt.Errorf("nested: %v", lib.Nest(nil)) // want `cannot verify FormatsNested: `
}

//@ Ensures result = nil <-> fine
