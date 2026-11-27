// Package getp hands a T whose Get returns a U whose N calls back. The
// cycle is not in what the call hands, but in what a call back returns; it
// is refused where verified code makes the U a value, so it needs no edge.
package getp

import "cycles/held/getq"

// T returns a U.
type T struct{}

// @Ensures True
func (T) Get() (i getq.I) { return U{} } // want `cannot verify Get: N may call through a function value or an interface value`

// U calls X.
type U struct{}

// @Variant 1
// @Ensures True
func (U) N() (n int) { return X() }

// X hands a T to getq.F.
//
// @Variant 0
// @Ensures True
func X() (n int) { return getq.F(T{}) }
