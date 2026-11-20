// Package linkedpull changes linkedlib.ErrA without naming it in Go, and
// does not import linkedlib.
package linkedpull

import (
	"errors"
	_ "unsafe"
)

//go:linkname errA linkedlib.ErrA
var errA error

// Clear sets linkedlib.ErrA to nil.
func Clear() { errA = nil }

// ErrPushed is given to another package by name.
//
//go:linkname ErrPushed
var ErrPushed = errors.New("pushed")

// Pushed relies on the value of a variable that a directive names.
//
// @Ensures r
func Pushed() (r bool) {
	return ErrPushed != nil // want `vego: cannot verify Pushed: ErrPushed is named by a go:linkname directive at pull.go:18, so it is not known to hold the error it was declared with`
}

// Local reads the variable that holds linkedlib.ErrA.
//
// @Ensures r
func Local() (r bool) {
	return errA != nil // want `vego: cannot verify Local: errA is named by a go:linkname directive at pull.go:10, so it is not known to hold the error it was declared with`
}
