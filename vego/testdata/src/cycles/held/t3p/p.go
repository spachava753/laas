// Package t3p fires t3q, whose hook, returned by the trusted
// t3lib.Current, is H (F9 of the review of step 0 of F43). Before, nothing
// was reported, and a main that set the hook to H and called X ran out of
// stack.
package t3p

import "cycles/held/t3q"

// H calls X.
//
// @Variant 1
// @Ensures True
func H() (n int) { return X() } // want `this call may not end: H calls X at p.go:\d+:\d+, X calls t3q\.Fire\(1\) at p.go:\d+:\d+, which may run H`

// X fires.
//
// @Variant 0
// @Ensures True
func X() (n int) { return t3q.Fire(1) } // want `this call may not end: X calls t3q\.Fire\(1\) at p.go:\d+:\d+, which may run X`
