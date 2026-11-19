// Package earlyalias hands an alias of an opaque variable that holds code of
// this package to another package while its variables are initialised.
package earlyalias

import "errors"

type codeErr struct{}

func (codeErr) Error() string { return "code" }

var errV error = codeErr{}

// ErrA holds errV, and so the methods of codeErr.
var ErrA = errV

var _ = errors.Unwrap(ErrA)

var ErrS = errors.New("s")

// Get returns a sentinel of the package.
//
// @Ensures err != nil
func Get() (err error) {
	return ErrS // want `vego: cannot verify Get: ErrS is not known to have its value yet when this runs: ErrA is handed to errors.Unwrap, which may call back into this package at earlyalias.go:\d+ while the variables of the package are initialised, which may run this function first`
}
