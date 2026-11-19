// Package vouched calls trusted functions whose contracts vouch for the
// errors they return, and twins of them whose contracts do not.
package vouched

import (
	"context"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
)

var errHidden = errors.New("hidden")

func next(s string, i int) (b byte, err error) {
	if i >= len(s) {
		return 0, io.EOF
	}
	return s[i], nil
}

func nextUnvouched(s string, i int) (b byte, err error) { return next(s, i) }

func open(name string) (err error) {
	if name == "" {
		return &fs.PathError{Op: "open", Path: name, Err: fs.ErrNotExist}
	}
	return nil
}

func two() (a, b error) { return nil, nil }

func log(e error) {}

func hidden() (err error) { return errHidden }

func late() (err error) { return context.DeadlineExceeded }

// Read wraps the error of next.
//
// @Requires 0 <= i
// @Ensures err = nil <-> i < |s|
// @Ensures is(err, io.EOF) <-> i >= |s|
func Read(s string, i int) (b byte, err error) {
	b, err = next(s, i)
	if err != nil {
		return 0, fmt.Errorf("read %d: %w", i, err)
	}
	return b, nil
}

// ReadUnvouched wraps the error of a function that does not vouch for it.
//
// @Requires 0 <= i
// @Ensures err = nil <-> i < |s|
func ReadUnvouched(s string, i int) (b byte, err error) {
	b, err = nextUnvouched(s, i)
	if err != nil {
		return 0, fmt.Errorf("read %d: %w", i, err) // want `vego: cannot verify ReadUnvouched: formatting err would run the methods of an error whose origin is not known`
	}
	return b, nil
}

// AtEnd asks errors.Is about the error of next.
//
// @Requires 0 <= i
// @Ensures end <-> i >= |s|
func AtEnd(s string, i int) (end bool) {
	_, err := next(s, i)
	return errors.Is(err, io.EOF)
}

// AtEndUnvouched asks it about the error of the twin.
//
// @Requires 0 <= i
// @Ensures True
func AtEndUnvouched(s string, i int) (end bool) {
	_, err := nextUnvouched(s, i)
	return errors.Is(err, io.EOF) // want `vego: cannot verify AtEndUnvouched: errors.Is would run the Is and Unwrap methods of err, an error whose origin is not known`
}

// AtEndWrong claims errors.Is finds another error.
//
// @Requires 0 <= i
// @Ensures end <-> i >= |s|
func AtEndWrong(s string, i int) (end bool) {
	_, err := next(s, i)
	return errors.Is(err, io.ErrUnexpectedEOF) // want `vego: postcondition may not hold: end <-> i >= |s|`
}

// Same compares the error of next with an error of which nothing is known.
//
// @Requires 0 <= i
// @Ensures True
func Same(s string, i int, other error) (same bool) {
	_, err := next(s, i)
	return err == other
}

// SameUnvouched does so with the error of the twin.
//
// @Requires 0 <= i
// @Ensures True
func SameUnvouched(s string, i int, other error) (same bool) {
	_, err := nextUnvouched(s, i)
	return err == other // want `vego: cannot verify SameUnvouched: comparing two errors can panic when both hold the same uncomparable type`
}

// Logs hands the error of next to a trusted function without runs.
//
// @Requires 0 <= i
// @Ensures True
func Logs(s string, i int) {
	_, err := next(s, i)
	log(err)
}

// LogsUnvouched hands it the error of the twin.
//
// @Requires 0 <= i
// @Ensures True
func LogsUnvouched(s string, i int) {
	_, err := nextUnvouched(s, i)
	log(err) // want `vego: cannot verify LogsUnvouched: err is passed to log, which is trusted, and is an error whose origin is not known`
}

// Passes returns the error of next, so that its own error is of known
// origin to its callers.
//
// @Requires 0 <= i
// @Ensures err = nil <-> i < |s|
// @Ensures err != nil -> err = io.EOF
func Passes(s string, i int) (b byte, err error) {
	return next(s, i)
}

// WrapsPassed wraps the error of Passes.
//
// @Requires 0 <= i
// @Ensures err = nil <-> i < |s|
func WrapsPassed(s string, i int) (err error) {
	_, err = Passes(s, i)
	if err != nil {
		return fmt.Errorf("passed: %w", err)
	}
	return nil
}

// Missing asks whether open failed for want of the file, by the name os
// gives fs.ErrNotExist.
//
// @Ensures name = "" -> missing
func Missing(name string) (missing bool) {
	err := open(name)
	return errors.Is(err, os.ErrNotExist)
}

// Second formats the second error of two, which two vouches for.
//
// @Ensures True
func Second() (err error) {
	_, b := two()
	if b == nil {
		return nil
	}
	return fmt.Errorf("second: %w", b)
}

// First formats the first, which it does not.
//
// @Ensures True
func First() (err error) {
	a, _ := two()
	return fmt.Errorf("first: %w", a) // want `vego: cannot verify First: formatting a would run the methods of an error whose origin is not known`
}

// Hidden compares with an unexported error variable that the contract of
// hidden names.
//
// @Ensures same
func Hidden() (same bool) {
	return hidden() == errHidden
}

// Late compares with an opaque variable that the contract of late names.
//
// @Ensures same
func Late() (same bool) {
	return late() == context.DeadlineExceeded
}

// QuotedInContract names a package by its path in quotes in a contract of
// its own, which only a trusted contract may do.
//
// @Ensures err != "io/fs".ErrNotExist // want `vego: in Ensures annotation: "io/fs".ErrNotExist: a package path in quotes can only be used in a trusted contract`
func QuotedInContract() (err error) {
	return nil
}

func vouchesParam(e error) error { return e }

func vouchesInt() (n int, err error) { return 0, nil }

func vouchesTwice() (err error) { return nil }

func vouchesUnknown() (err error) { return nil }

func namesQuotedShort() (err error) { return io.EOF }

func namesMissingPackage() (err error) { return nil }

func namesMissingVariable() (err error) { return nil }

// Defective calls the functions whose entries cannot be used.
//
// @Ensures True
func Defective() {
	_ = vouchesParam(nil) // want `vouches "e": e is not a result` `cannot verify Defective`
}

// DefectiveInt calls one that lists a result of type int.
//
// @Ensures True
func DefectiveInt() {
	_, _ = vouchesInt() // want `its vouches lists n, whose type int is not error` `cannot verify DefectiveInt`
}

// DefectiveTwice calls one that lists a result twice.
//
// @Ensures True
func DefectiveTwice() {
	_ = vouchesTwice() // want `its vouches lists err twice` `cannot verify DefectiveTwice`
}

// DefectiveUnknown calls one that lists a name it does not have.
//
// @Ensures True
func DefectiveUnknown() {
	_ = vouchesUnknown() // want `its vouches "failure": failure is not a result` `cannot verify DefectiveUnknown`
}

// QuotedShort calls one that writes io.EOF in quotes.
//
// @Ensures True
func QuotedShort() {
	_ = namesQuotedShort() // want `in its ensures "err = \\"io\\".EOF": "io".EOF: write io.EOF, without quotes` `cannot verify QuotedShort`
}

// MissingPackage calls one that names a package not in the build.
//
// @Ensures True
func MissingPackage() {
	_ = namesMissingPackage() // want `"example.com/none".ErrNone: package example.com/none is not in the build of this package` `cannot verify MissingPackage`
}

// MissingVariable calls one that names a variable io does not have.
//
// @Ensures True
func MissingVariable() {
	_ = namesMissingVariable() // want `package io has no package-level error variable ErrNone` `cannot verify MissingVariable`
}
