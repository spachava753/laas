// Package wrapsp has a sentinel that wraps io.EOF, and a proof that relies
// on what went into it.
package wrapsp

import (
	"fmt"
	"io"
)

var ErrRead = fmt.Errorf("read: %w", io.EOF)

// Wrap formats ErrRead, which only an error of known origin may be.
//
// @Ensures err = nil <-> ok
func Wrap(ok bool) (err error) {
	if ok {
		return nil
	}
	return fmt.Errorf("wrap: %w", ErrRead)
}
