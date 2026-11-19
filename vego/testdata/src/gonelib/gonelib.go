// Package gonelib has a verified function whose proof relies on its
// sentinel being the error it was declared with.
package gonelib

import "errors"

var ErrGone = errors.New("gone")

// ErrOpaque is an opaque variable, and ErrAliased an alias of ErrTarget.
type goneErr struct{}

func (goneErr) Error() string { return "gone" }

var (
	ErrOpaque  error = goneErr{}
	ErrTarget        = errors.New("target")
	ErrAliased       = ErrTarget
)

// Same relies on ErrOpaque and on what ErrAliased holds.
//
// @Ensures same
func Same() (same bool) {
	return ErrOpaque != nil && ErrAliased == ErrTarget
}

// Fail fails unless told otherwise.
//
// @Ensures err = nil <-> ok
func Fail(ok bool) (err error) {
	if ok {
		return nil
	}
	return ErrGone
}
