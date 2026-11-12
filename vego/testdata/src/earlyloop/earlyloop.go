// Package earlyloop puts a value of its own, in a range clause, into a variable of another
// package and has that package call it, while its own variables are being
// initialised.
package earlyloop

import (
	"errors"
	"gen"
)

// T has a method that reads a variable of the package.
type T struct{}

// Check is called by gen.Run before ErrX has its value.
func (T) Check() bool {
	return ErrX != nil // want `vego: cannot verify Check: ErrX is not known to have its value yet when this runs: gen.Box.Value is assigned, which another package may read at earlyloop.go:\d+ while the variables of the package are initialised, which may run this function first`
}

//@ Ensures result

func seed() bool {
	for _, gen.Box.Value = range []T{{}} {
	}
	return gen.Run(gen.GetBox())
}

// First is computed before ErrX is set.
var First = seed()

// ErrX would be known not to be nil in a package that did not do this.
var ErrX = errors.New("x")
