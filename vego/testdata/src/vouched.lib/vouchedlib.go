// Package vouchedlib, at a path with a dot in it, has trusted functions
// whose contracts name its own error variable and one of io.
package vouchedlib

import (
	"errors"
	"io"
)

var ErrBad = errors.New("bad")

// Fail returns ErrBad for a negative n.
func Fail(n int) (err error) {
	if n < 0 {
		return ErrBad
	}
	return nil
}

// FailQuoted is the same, with a contract that names ErrBad by the path of
// the package in quotes.
func FailQuoted(n int) (err error) { return Fail(n) }

// End returns io.EOF.
func End() (err error) { return io.EOF }
