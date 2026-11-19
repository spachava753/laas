// Package earlyaliasok hands aliases of sentinels to another package while
// its variables are initialised, which runs no code of this package.
package earlyaliasok

import (
	"errors"
	"io"
)

var ErrS = errors.New("s")

var (
	ErrA = ErrS
	ErrB = errS()
	ErrC = io.EOF
)

func errS() error { return ErrS }

var (
	_ = errors.Unwrap(ErrA)
	_ = errors.Unwrap(ErrB)
	_ = errors.Unwrap(ErrC)
)

// Get returns a sentinel of the package.
//
// @Ensures err != nil
func Get() (err error) { // want `the contract of Get may also be met by a function that always returns an error`
	return ErrS
}
