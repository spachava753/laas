// Package globalsleakclient relies on the contents of a table of another
// package, which a third package it is built with lets out.
package globalsleakclient // want `vego: globalslib.Plans is changed at leak.go:10 in package globalsleak, which this package is built with, but proofs in package globalslib rely on what it refers to being only read`

import (
	"globalsleak"
	"globalslib"
)

var _ = globalsleak.Leak

// Pro would be 1000 if what Plans refers to were only read.
//
// @Ensures r = 1000
func Pro() (r int) {
	return globalslib.Plans["pro"] // want `^vego: postcondition may not hold: r = 1000; the contents of globalslib.Plans are not known to stay as initialised: the use at leak.go:10 in package globalsleak lets a reference to them out$`
}
