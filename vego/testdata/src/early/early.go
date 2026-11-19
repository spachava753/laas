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

// Named names ErrX in its contract, which says nothing true about the
// value it may have when this runs.
//
// @Ensures err != ErrX // want `vego: in Ensures annotation: ErrX is not known to have its value yet when this runs`
func Named() (err error) {
	return nil
}

// ErrAliasX holds ErrX, and ErrOpaqueX holds something else; neither is
// known to have its value yet either.
var (
	ErrAliasX        = ErrX
	ErrOpaqueX error = T{}.err()
)

func (T) err() error { return nil }

// concreteErr makes an opaque variable that is not nil once it is set.
type concreteErr struct{}

func (concreteErr) Error() string { return "concrete" }

// ErrConcreteX would be known not to be nil in a package that did not run
// its own code while its variables are initialised.
var ErrConcreteX error = concreteErr{}

// Concrete reads it alone.
//
// @Ensures r
func Concrete() (r bool) {
	return ErrConcreteX != nil // want `vego: cannot verify Concrete: ErrConcreteX is not known to have its value yet when this runs`
}

// Aliased reads them.
//
// @Ensures True
func Aliased() (a, b error) {
	return ErrAliasX, ErrOpaqueX // want `vego: cannot verify Aliased: ErrAliasX is not known to have its value yet when this runs`
}
