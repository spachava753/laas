// Package sibtp calls a hook it is handed; it does not import sibtq, and
// sibtq does not import it. Code that is not verified may set sibtlib's
// hook to H and hand sibtq.Fire to SetF: X runs Fire, which runs the hook
// that the trusted sibtlib.Current returns, which calls X. It is the limit
// "What a proof assumes" states. Verified code that wires them is refused
// (sibtw).
package sibtp

import "cycles/held/sibti"

var f sibti.Fn

// SetF is not verified.
func SetF(g sibti.Fn) { f = g }

// H calls X.
//
// @Variant 1
// @Ensures True
func H() (n int) { return X(0, 0) }

// X calls the hook f.
//
// @Variant 0
// @Ensures True
func X(a, b int) (n int) {
	if f != nil {
		return f(1)
	}
	return 0
}
