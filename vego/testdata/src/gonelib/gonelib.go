// Package gonelib has a verified function whose proof relies on its
// sentinel being the error it was declared with.
package gonelib

import "errors"

var ErrGone = errors.New("gone")

// Fail fails unless told otherwise.
//
// @Ensures err = nil <-> ok
func Fail(ok bool) (err error) {
	if ok {
		return nil
	}
	return ErrGone
}
