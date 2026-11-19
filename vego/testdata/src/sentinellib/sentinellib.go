// Package sentinellib has verified functions whose contracts say which
// error they return.
package sentinellib

import (
	"errors"
	"io"
)

var (
	ErrGone   = errors.New("gone")
	errHidden = errors.New("hidden")
)

// Find fails with ErrGone for a negative key.
//
// @Ensures err = nil <-> k >= 0
// @Ensures err = ErrGone <-> k < 0
// @Ensures err = nil -> v = k
func Find(k int) (v int, err error) {
	if k < 0 {
		return 0, ErrGone
	}
	return k, nil
}

// Hidden fails with an error the importer cannot name.
//
// @Ensures err = nil <-> ok
// @Ensures err != nil -> err = errHidden
func Hidden(ok bool) (err error) {
	if ok {
		return nil
	}
	return errHidden
}

// End fails with a sentinel of a third package.
//
// @Ensures err = nil <-> ok
// @Ensures err != nil -> err = io.EOF
func End(ok bool) (err error) {
	if ok {
		return nil
	}
	return io.EOF
}
