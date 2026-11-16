// Package earlytype has its own code run, through a type argument, while
// its variables are being initialised.
package earlytype

import (
	"errors"
	"gen"
)

// T has a method that reads a variable of the package.
type T struct{}

// Ready is called by gen.Call before ErrX has its value.
//
// @ Ensures result
func (T) Ready() (result bool) {
	return ErrX != nil // want `vego: cannot verify Ready: ErrX is not known to have its value yet when this runs: the type earlytype.T is handed to gen.Call, which may call its methods at earlytype.go:\d+ while the variables of the package are initialised, which may run this function first`
}

// First is computed before ErrX is set.
var First = gen.Call[T]()

// ErrX would be known not to be nil in a package that did not do this.
var ErrX = errors.New("x")
