// Package sibvp calls a hook it is handed; it does not import sibvs, and
// sibvs does not import it. Code that is not verified may register H in
// sibvs and hand sibvs.Fire to SetF: X runs Fire, which runs H, which calls
// X. Neither package sees the other, so neither graph has the cycle: the
// limit "What a proof assumes" states (F12 of the review of step 0 of
// F43). Verified code that wires them is refused (sibvw).
package sibvp

import "cycles/held/sibvi"

var f sibvi.Fn

// SetF is not verified.
func SetF(g sibvi.Fn) { f = g }

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
