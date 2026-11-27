// Package sibr wraps an I; it does not import sibp.
package sibr

import "cycles/held/sibi"

// T wraps an I.
type T struct{ inner sibi.I }

// Wrap wraps x.
//
// @Ensures True
func Wrap(x sibi.I) (t T) { return T{inner: x} }

// M calls N of what it wraps.
//
// @Ensures True
func (t T) M() (n int) {
	if t.inner == nil {
		return 0
	}
	return t.inner.N()
}
