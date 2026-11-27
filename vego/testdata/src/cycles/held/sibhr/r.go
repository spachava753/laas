// Package sibhr wraps an I; nothing in p or q imports it.
package sibhr

import "cycles/held/sibhi"

// T wraps an I.
type T struct{ inner sibhi.I }

// Wrap wraps x.
//
// @Ensures True
func Wrap(x sibhi.I) (t T) { return T{inner: x} }

// M calls N of what it wraps.
//
// @Ensures True
func (t T) M() (n int) {
	if t.inner == nil {
		return 0
	}
	return t.inner.N()
}
