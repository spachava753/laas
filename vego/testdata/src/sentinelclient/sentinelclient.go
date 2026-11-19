// Package sentinelclient calls functions whose contracts name error
// variables of their own package. It has an ErrGone of its own, which is
// another error.
package sentinelclient

import (
	"errors"
	"io"

	"sentinellib"
)

var ErrGone = errors.New("client gone")

// Look passes on the error of Find, and says which one it is.
//
// @Ensures err = nil <-> k >= 0
// @Ensures err = sentinellib.ErrGone <-> k < 0
func Look(k int) (v int, err error) {
	return sentinellib.Find(k)
}

// LookOwn claims the error is the ErrGone of this package.
//
// @Ensures err = nil <-> k >= 0
// @Ensures err = ErrGone <-> k < 0
func LookOwn(k int) (v int, err error) {
	return sentinellib.Find(k) // want `vego: postcondition may not hold: err = ErrGone <-> k < 0`
}

// Gone compares with the sentinel of the other package.
//
// @Ensures gone <-> k < 0
func Gone(k int) (gone bool) {
	_, err := sentinellib.Find(k)
	return err == sentinellib.ErrGone
}

// NotOwn knows that the error of the other package is not the one of this
// package.
//
// @Ensures same = False
func NotOwn(k int) (same bool) {
	_, err := sentinellib.Find(k)
	return err == ErrGone
}

// Hidden knows the error is the one the other package means, which it
// cannot name, so it is not ErrGone of either package.
//
// @Ensures err = nil <-> ok
// @Ensures err != sentinellib.ErrGone And err != ErrGone
func Hidden(ok bool) (err error) {
	return sentinellib.Hidden(ok)
}

// End knows the error is io.EOF.
//
// @Ensures eof <-> ~ok
func End(ok bool) (eof bool) {
	return sentinellib.End(ok) == io.EOF
}
