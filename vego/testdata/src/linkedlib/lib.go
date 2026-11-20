// Package linkedlib declares an error variable that nothing in it changes.
// Package linkedpull gives the same storage to a variable of its own with
// a go:linkname directive, and changes it.
package linkedlib

import "errors"

var ErrA = errors.New("a")

// NotNil relies on ErrA.
//
// @Ensures r
func NotNil() (r bool) { return ErrA != nil }
