// Package funcvaluesinitmethod hands, while its variables are initialised, a
// method value of its own to a function of another package, which may call
// it, so it relies on none of its error variables.
package funcvaluesinitmethod

import (
	"errors"
	"funcvalueslib"
)

type stepper struct{}

// Step takes a step.
//
// @Requires 0 <= x <= 100
// @Ensures x <= y <= x + 100
func (stepper) Step(x int) (y int) {
	return x
}

var stepped = funcvalueslib.Run(stepper{}.Step, 1)

var ErrX = errors.New("x")

// Known is 1 because ErrX is not nil, which is known only in a package
// where no code of the package can run before ErrX has its value.
//
// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil { // want `vego: cannot verify Known: ErrX is not known to have its value yet when this runs: stepper\{\}.Step is handed to funcvalueslib.Run, which may call back into this package`
		return 1
	}
	return 0
}
