// Package funcvaluesinitlit hands, while its variables are initialised, a
// function literal to a function of its own that calls through it, so it
// relies on none of its error variables.
package funcvaluesinitlit

import "errors"

// @Requires 0 <= x <= 100
// @Ensures x <= y
type Step func(x int) (y int)

// Run takes one step.
//
// @Requires s != nil
// @Ensures y >= 1
func Run(s Step) (y int) {
	return s(1)
}

var ran = Run(func(x int) int { return x })

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
