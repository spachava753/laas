// Package tv2p hands its J to a trusted tv2lib.Run, whose entry claims it
// calls only M (X3), or to tv2lib.Run2, silent under asserts (X4). What
// either runs may be a tv2u.T, whose M calls tv2v.Fire, which runs the hook
// it keeps (F14 of the review of step 1 of F43). Before, X3 verified and ran
// out of stack.
package tv2p

import (
	"cycles/held/tv2i"
	"cycles/held/tv2lib"
	"cycles/held/tv2v"
)

var saved tv2i.J

// Setup is not verified.
func Setup(x tv2i.J) { saved = x; tv2v.Register(H3); tv2v.Register(H4) }

// H3 calls X3.
//
// @Variant 1
// @Ensures True
func H3() (n int) {
	if saved == nil {
		return 0
	}
	return X3(saved) // want `this call may not end: H3 calls X3 at p.go:\d+:\d+, X3 calls tv2lib\.Run\(x\) at p.go:\d+:\d+, which may run H3`
}

// X3 hands x to tv2lib.Run, whose entry claims it calls only M.
//
// @Requires x != nil
// @Variant 0
// @Ensures True
func X3(x tv2i.J) (n int) { return tv2lib.Run(x) } // want `this call may not end: X3 calls tv2lib\.Run\(x\) at p.go:\d+:\d+, which may run H3, H3 calls X3 at p.go:\d+:\d+`

// H4 calls X4.
//
// @Variant 1
// @Ensures True
func H4() (n int) {
	if saved == nil {
		return 0
	}
	return X4(saved) // want `this call may not end: H4 calls X4 at p.go:\d+:\d+, X4 hands x to tv2lib\.Run2\(x\) at p.go:\d+:\d+, which may run H4`
}

// X4 hands x to tv2lib.Run2, whose entry is silent under asserts.
//
// @Requires x != nil
// @Variant 0
// @Ensures True
func X4(x tv2i.J) (n int) { return tv2lib.Run2(x) } // want `this call may not end: X4 hands x to tv2lib\.Run2\(x\) at p.go:\d+:\d+, which may run X4` `cannot verify X4: code that the call may run writes saved, which cannot be followed: saved has type cycles/held/tv2i\.J, which has no states`
