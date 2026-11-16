// Package earlyrange has its own code run, by ranging over a function,
// while its variables are being initialised.
package earlyrange

import "errors"

// T has a method that reads a variable of the package.
type T struct{}

// Ok is called, through All, before ErrX has its value.
//
// @ Ensures result
func (T) Ok() (result bool) {
	return ErrX != nil // want `vego: cannot verify Ok: ErrX is not known to have its value yet when this runs: a function that is not a named function of this package is ranged over at earlyrange.go:\d+ while the variables of the package are initialised, which may run this function first`
}

// All yields what Ok says.
func (t T) All(yield func(bool) bool) { yield(t.Ok()) }

// Seqer hides which All is ranged over.
type Seqer interface{ All(func(bool) bool) }

var s Seqer = T{}

func first() bool {
	for v := range s.All {
		return v
	}
	return true
}

// First is computed before ErrX is set.
var First = first()

// ErrX would be known not to be nil in a package that did not do this.
var ErrX = errors.New("x")
