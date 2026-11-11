// Package settled initialises its variables with calls that Go's ordering
// follows, so its error variables have their values before any of its
// functions can run.
package settled

import (
	"errors"
	"strings"
)

func twice(s string) string { return s + s }

// Name is computed by calls that Go follows.
var Name = twice(strings.ToUpper("x"))

// Later is a function kept for later; writing it down runs nothing.
var Later = func(f func()) { f() }

// ErrY is set before anything else of the package runs.
var ErrY = errors.New("y")

// Ok reports that it is.
func Ok() bool {
	return ErrY != nil
}

//@ Ensures result
