// Package lockspred declares a predicate with the name of a state.
package lockspred

import "sync"

// @Predicate held(x) ::= x > 0

// @Requires m != nil And held(m) // want `held is both a predicate and a state of m; rename the predicate`
// @Ensures True
func Ambiguous(m *sync.Mutex) {
}

// @Requires held(n)
// @Ensures True
func Number(n int) {
}
