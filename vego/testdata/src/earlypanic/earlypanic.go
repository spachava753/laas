// Package earlypanic panics, while its variables are being initialised,
// with a value of its own, which the runtime then asks for its text.
package earlypanic

import "errors"

// T is an error whose text depends on a variable of the package.
type T struct{}

// Error is called by the runtime before ErrX has its value.
//
// @Ensures result = "ready"
func (T) Error() (result string) {
	if ErrX != nil { // want `vego: cannot verify Error: ErrX is not known to have its value yet when this runs: something of this package is handed to panic at earlypanic.go:\d+ while the variables of the package are initialised, which may run this function first`
		return "ready"
	}
	return "early"
}

func start() int { panic(T{}) }

// First is computed before ErrX is set.
var First = start()

// ErrX would be known not to be nil in a package that did not do this.
var ErrX = errors.New("x")
