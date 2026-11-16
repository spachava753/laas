// Package earlycarrier hands another package a value of that package's own
// generic type, instantiated with a type of this package, while its
// variables are being initialised.
package earlycarrier

import (
	"errors"
	"gen"
)

// T has a method that reads a variable of the package.
type T struct{}

// Check is called through gen.Carrier before ErrX has its value.
//
// @ Ensures result
func (T) Check() (result bool) {
	return ErrX != nil // want `vego: cannot verify Check: ErrX is not known to have its value yet when this runs: gen.Carrier\[T\]\{\} is handed to gen.Run, which may call back into this package at earlycarrier.go:\d+ while the variables of the package are initialised, which may run this function first`
}

// First is computed before ErrX is set.
var First = gen.Run(gen.Carrier[T]{})

// ErrX would be known not to be nil in a package that did not do this.
var ErrX = errors.New("x")
