// Package wrapped holds package-level errors that wrap other errors. Such
// an error is not nil whatever it wraps, but its origin is known only if
// nothing went into it that brings code of its own: with %w the wrapped
// error stays inside, where Unwrap finds it.
package wrapped

import (
	"errors"
	"fmt"
	"context"
	"io"

	"lib"
)

var (
	errBase    = errors.New("base")
	errOver    = fmt.Errorf("over: %w", errBase)
	errCounted = fmt.Errorf("%d over: %w", 3, errOver)
	errEOF     = fmt.Errorf("eof: %w", io.EOF)
	errForeign = fmt.Errorf("foreign: %w", context.DeadlineExceeded)
	errOnTop   = fmt.Errorf("on top: %w", errForeign)
	errNumbers = fmt.Errorf("numbers: %v", [][]int{{1}, {2}})
	errNested  = fmt.Errorf("nested: %v", lib.Nest(nil))
)

func tell(e error) {}

// TellsOwn passes errors into which only errors of this package went.
//
// @Ensures True
func TellsOwn() {
	tell(errBase)
	tell(errOver)
	tell(errCounted)
}

// TellsEOF passes one that holds an error of another package that is a
// sentinel there, made by errors.New.
//
// @Ensures True
func TellsEOF() {
	tell(errEOF)
}

// TellsForeign passes one that holds an error of another package that is
// not known to be one: context.DeadlineExceeded holds a value that is not
// made by errors.New or fmt.Errorf.
//
// @Ensures True
func TellsForeign() {
	tell(errForeign) // want `cannot verify TellsForeign: errForeign is passed to tell, which is trusted, and is an error whose origin is not known`
}

// TellsOnTop passes one that holds it one step further in.
//
// @Ensures True
func TellsOnTop() {
	tell(errOnTop) // want `cannot verify TellsOnTop: errOnTop is passed to tell, which is trusted, and is an error whose origin is not known`
}

// FormatsForeign wraps it again, which would run its methods.
//
// @Ensures result = nil <-> fine
func FormatsForeign(fine bool) (result error) {
	if fine {
		return nil
	}
	return fmt.Errorf("again: %w", errForeign) // want `cannot verify FormatsForeign: formatting errForeign would run the methods of an error whose origin is not known`
}

// FormatsOwn wraps one of this package.
//
// @Ensures result = nil <-> fine
func FormatsOwn(fine bool) (result error) {
	if fine {
		return nil
	}
	return fmt.Errorf("again: %w", errCounted)
}

// ReturnsForeign only hands it on. It is not nil, whatever it holds.
//
// @Ensures result = nil <-> fine
func ReturnsForeign(fine bool) (result error) {
	if fine {
		return nil
	}
	return errForeign
}

// TellsNumbers passes an error into which slices of slices of numbers went.
//
// @Ensures True
func TellsNumbers() {
	tell(errNumbers)
}

// TellsNested passes one made from a slice type that is its own element
// type, which holds nothing plain however far it is followed.
//
// @Ensures True
func TellsNested() {
	tell(errNested) // want `cannot verify TellsNested: errNested is passed to tell, which is trusted, and is an error whose origin is not known`
}

// FormatsNested formats such a value in verified code.
//
// @Ensures result = nil <-> fine
func FormatsNested(fine bool) (result error) {
	if fine {
		return nil
	}
	return fmt.Errorf("nested: %v", lib.Nest(nil)) // want `cannot verify FormatsNested: `
}
