// Package linkedpullnear imports linkedlib and gives the storage of its
// error variable to a variable of its own with a go:linkname directive.
package linkedpullnear

import (
	"linkedlib"
	_ "unsafe"
)

//go:linkname errA linkedlib.ErrA // want `vego: linkedlib.ErrA may be changed here, but proofs in package linkedlib rely on it being the error it was declared with`
var errA error

// Clear sets linkedlib.ErrA to nil.
func Clear() { errA = nil }

// NotNil relies on linkedlib.ErrA.
//
// @Ensures r
func NotNil() (r bool) {
	return linkedlib.ErrA != nil // want `vego: cannot verify NotNil: linkedlib.ErrA is named by a go:linkname directive at near.go:10 in this package, so it is not known to hold the error it was declared with`
}
