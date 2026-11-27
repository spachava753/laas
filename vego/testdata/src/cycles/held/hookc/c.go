// Package hookc calls hookb.Fire one level down: G reads no variable
// itself, but calls a function of another package that does. G is itself
// a function that code which is not verified may register.
package hookc

import "cycles/held/hookb"

// @Ensures True
func G() (n int) { return hookb.Fire(2) } // want `this call may not end: G calls hookb\.Fire\(2\) at c.go:\d+:\d+, which may run G`
