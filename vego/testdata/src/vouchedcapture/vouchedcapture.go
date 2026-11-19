// Package vouchedcapture calls trusted functions of another package whose
// contracts name ErrBad and io.EOF. It has an ErrBad of its own, and calls
// another package io, so the names in those contracts must not be read as
// its own.
package vouchedcapture

import (
	"errors"
	io "fakeio"

	vouchedlib "vouched.lib"
)

var ErrBad = errors.New("capture bad")

// Theirs finds the ErrBad of vouchedlib.
//
// @Requires n < 0
// @Ensures r
func Theirs(n int) (r bool) {
	return errors.Is(vouchedlib.Fail(n), vouchedlib.ErrBad) && errors.Is(vouchedlib.FailQuoted(n), vouchedlib.ErrBad)
}

// Ours does not find the ErrBad of this package.
//
// @Requires n < 0
// @Ensures ~r
func Ours(n int) (r bool) {
	return errors.Is(vouchedlib.Fail(n), ErrBad)
}

// FakeEnd: End returns the io.EOF of the standard library, not the EOF of
// the package this file calls io.
//
// @Ensures ~same
func FakeEnd() (same bool) {
	return vouchedlib.End() == io.EOF
}
