// Package t1p calls M of what it is handed (F8 of the review of step 0 of
// F43). t1r.T.M, which it can see, runs what it wraps through the trusted
// t1lib.Run, whose entry says Run calls N. Before, nothing was reported, and
// Wire ran out of stack.
package t1p

import (
	"cycles/held/t1i"
	"cycles/held/t1r"
)

// PT calls X back.
type PT struct{ J t1i.J }

// N calls X.
//
// @Requires t != nil
// @Variant 1
// @Ensures True
func (t *PT) N() (n int) { return X(t.J) } // want `this call may not end: \(\*PT\)\.N calls X at p.go:\d+:\d+, X calls x\.M\(\) at p.go:\d+:\d+, which may run \(\*PT\)\.N`

// X calls x.M().
//
// @Variant 0
// @Ensures True
func X(x t1i.J) (n int) {
	if x == nil {
		return 0
	}
	return x.M() // want `this call may not end: X calls x\.M\(\) at p.go:\d+:\d+, which may run \(\*PT\)\.N, \(\*PT\)\.N calls X at p.go:\d+:\d+`
}

// Wire is not verified.
func Wire() int {
	pt := &PT{}
	var x t1i.J = t1r.Wrap(pt)
	pt.J = x
	return X(x)
}
