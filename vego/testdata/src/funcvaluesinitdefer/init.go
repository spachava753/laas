// Package funcvaluesinitdefer calls, while its variables are initialised, a
// function that defers a call through a function value, so it relies on
// none of its error variables.
package funcvaluesinitdefer

import "errors"

// Close is called when something ends.
//
// @Ensures True
type Close func()

// Finish defers the call of what it is given.
//
// @Requires c != nil
// @Ensures n = 0
func Finish(c Close) (n int) {
	defer c()
	return 0
}

func closer() {}

var finished = Finish(closer)

var ErrX = errors.New("x")

// Known is 1 because ErrX is not nil, which is known only in a package
// where no code of the package can run before ErrX has its value.
//
// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil { // want `vego: cannot verify Known: ErrX is not known to have its value yet when this runs: a function value or an interface method is called at init.go:\d+ while the variables of the package are initialised`
		return 1
	}
	return 0
}
