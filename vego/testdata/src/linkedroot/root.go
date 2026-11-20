// Package linkedroot is built with linkedlib and linkedpull, and is where
// the change and the proofs that rely on the variable meet.
package linkedroot // want `vego: linkedlib.ErrA is changed at pull.go:10 in package linkedpull, which this package is built with, but proofs in package linkedlib rely on it being the error it was declared with`

import (
	"linkedlib"
	_ "linkedpull"
)

// NotNil relies on linkedlib.ErrA.
//
// @Ensures r
func NotNil() (r bool) {
	return linkedlib.ErrA != nil // want `vego: cannot verify NotNil: linkedlib.ErrA is changed at pull.go:10 in package linkedpull, which this package is built with, so it is not known to hold the error it was declared with`
}
