// Package vouchedclient formats an error that a verified function of
// another package passes on from a trusted function that vouches for it.
package vouchedclient

import (
	"errors"
	"fmt"
	"io"

	"vouched"
)

// Wraps wraps the error of vouched.Passes.
//
// @Requires 0 <= i
// @Ensures err = nil <-> i < |s|
// @Ensures is(err, io.EOF) <-> i >= |s|
func Wraps(s string, i int) (err error) {
	_, err = vouched.Passes(s, i)
	if err != nil {
		return fmt.Errorf("client: %w", err)
	}
	return nil
}

// AtEnd asks errors.Is about it.
//
// @Requires 0 <= i
// @Ensures end <-> i >= |s|
func AtEnd(s string, i int) (end bool) {
	_, err := vouched.Passes(s, i)
	return errors.Is(err, io.EOF)
}
