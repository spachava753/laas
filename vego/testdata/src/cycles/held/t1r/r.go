// Package t1r wraps an I and runs it through lib.
package t1r

import (
	"cycles/held/t1i"
	"cycles/held/t1lib"
)

// T wraps an I.
type T struct{ inner t1i.I }

// Wrap wraps x.
//
// @Ensures True
func Wrap(x t1i.I) (t T) { return T{inner: x} }

// M runs what it wraps through t1lib.Run.
//
// @Ensures True
func (t T) M() (n int) {
	if t.inner == nil {
		return 0
	}
	return t1lib.Run(t.inner)
}
