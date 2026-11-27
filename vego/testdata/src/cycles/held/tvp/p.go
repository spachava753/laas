// Package tvp sees tvv; it hands its J to tvq.F (X) or calls M itself (X2)
// (F14 of the review of step 1 of F43). Code that is not verified may hand
// it a tvu.T, whose M calls tvv.Fire, a verified function that runs the hook
// it keeps in a variable, which may be H or H2. Before, X2 verified at the
// base and X since the summaries, and both ran out of stack.
package tvp

import (
	"cycles/held/tvi"
	"cycles/held/tvq"
	"cycles/held/tvv"
)

var saved tvi.J

// Setup is not verified.
func Setup(x tvi.J) { saved = x; tvv.Register(H); tvv.Register(H2) }

// H calls X with what Setup saved.
//
// @Variant 1
// @Ensures True
func H() (n int) {
	if saved == nil {
		return 0
	}
	return X(saved) // want `this call may not end: H calls X at p.go:\d+:\d+, X calls tvq\.F\(x\) at p.go:\d+:\d+, which may run H`
}

// X hands x to tvq.F.
//
// @Variant 0
// @Ensures True
func X(x tvi.J) (n int) { return tvq.F(x) } // want `this call may not end: X calls tvq\.F\(x\) at p.go:\d+:\d+, which may run H, H calls X at p.go:\d+:\d+`

// H2 calls X2 with what Setup saved.
//
// @Variant 1
// @Ensures True
func H2() (n int) {
	if saved == nil {
		return 0
	}
	return X2(saved) // want `this call may not end: H2 calls X2 at p.go:\d+:\d+, X2 calls x\.M\(\) at p.go:\d+:\d+, which may run H2`
}

// X2 calls x.M() itself.
//
// @Variant 0
// @Ensures True
func X2(x tvi.J) (n int) {
	if x == nil {
		return 0
	}
	return x.M() // want `this call may not end: X2 calls x\.M\(\) at p.go:\d+:\d+, which may run H2, H2 calls X2 at p.go:\d+:\d+`
}
