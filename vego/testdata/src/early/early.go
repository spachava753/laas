// Package early runs its own code, through an interface, while its
// variables are being initialised.
package early

import "fmt"

// T has a method that reads a variable of the package.
type T struct{}

// Ok reports whether the variable is set. Called through the interface
// below it runs before the variable has its value, and returns false.
//
// @Ensures result
func (T) Ok() (result bool) {
	return ErrX != nil // want `vego: cannot verify Ok: ErrX is not known to have its value yet when this runs: a function value or an interface method is called at early.go:\d+ while the variables of the package are initialised, which may run this function first`
}

// Checker hides which method is called.
type Checker interface{ Ok() bool }

var checker Checker = T{}

// First is computed before ErrX is set.
var First = checker.Ok()

// ErrX would be known not to be nil in a package that did not do this.
var ErrX = fmt.Errorf("x %d", 1)
