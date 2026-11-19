// Package usesearly reads an error variable of a package whose own code can
// run before the variable is set. Code of this package runs only once that
// package is initialised, so here the variable has its value.
package usesearly

import "early"

// Fail fails with ErrX unless told otherwise.
//
// @Ensures err = nil <-> ok
// @Ensures err != nil -> err = early.ErrX
func Fail(ok bool) (err error) {
	if ok {
		return nil
	}
	return early.ErrX
}
