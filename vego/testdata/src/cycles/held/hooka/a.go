// Package hooka registers a hook that calls back into X through
// hookb.Fire. Before F43 the call of Fire, which hands nothing, had no edge,
// and X and h verified while a program that calls Setup and then X ran out
// of stack.
package hooka

import "cycles/held/hookb"

// h calls X.
//
// @Variant 1
// @Ensures True
func h() (n int) { return X() } // want `this call may not end: h calls X at a.go:\d+:\d+, X calls hookb.Fire\(1\) at a.go:\d+:\d+, which may run h; Fire reads a package-level variable that can hold code`

// Setup registers h; it is not verified.
func Setup() {
	hookb.Register(h)
}

// X fires.
//
// @Variant 0
// @Ensures True
func X() (n int) {
	return hookb.Fire(1) // want `this call may not end: X calls hookb.Fire\(1\) at a.go:\d+:\d+, which may run X; Fire reads a package-level variable that can hold code`
}
