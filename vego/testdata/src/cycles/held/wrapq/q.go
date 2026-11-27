// Package wrapq calls M of what it is handed. wrapr.T.M, which runs what it
// wraps, is an implementation of it that wrapq can see, and that may run a
// wrapq.F made into a value by code that is not verified, so F is a cycle
// by the types alone.
package wrapq

import "cycles/held/wrapr"

// @Requires x != nil
// @Ensures True
func F(x wrapr.I) { x.M() }
