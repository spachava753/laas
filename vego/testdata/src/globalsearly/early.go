// Package globalsearly runs its own code, through an interface, while its
// variables are being initialised.
package globalsearly

// T has a method that reads variables of the package.
type T struct{}

// Limit reads a variable that may not have its value yet when this runs.
//
// @Ensures r = 10
func (T) Limit() (r int) {
	return limit // want `vego: cannot verify Limit: limit is not known to have its value yet when this runs: a function value or an interface method is called at early.go:\d+ while the variables of the package are initialised, which may run this function first`
}

// Zero reads a variable without an initialiser, which is zero before any
// code of the package runs, and stays so.
//
// @Ensures r = 0
func (T) Zero() (r int) { return zero }

// Limiter hides which method is called.
type Limiter interface{ Limit() int }

var limiter Limiter = T{}

// First is computed before limit is set.
var First = limiter.Limit()

var limit = 10

var zero int
