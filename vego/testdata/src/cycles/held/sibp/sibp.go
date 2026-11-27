// Package sibp calls M of what it is handed; it does not import sibr,
// and sibr does not import it (sib of the review of the design of F43).
// Code that is not verified may wrap a PT in a sibr.T and hand it to X:
// X calls T.M, which calls PT.N, which calls X. Neither package can see
// the other, so neither graph has the cycle, and X and N verify. It is the
// limit that "What a proof assumes" states for packages that do not import
// each other. Verified code that wires them is refused (sibw).
package sibp

import "cycles/held/sibi"

// PT calls X back.
type PT struct{ J sibi.J }

// N calls X.
//
// @Requires t != nil
// @Variant 1
// @Ensures True
func (t *PT) N() (n int) { return X(t.J) }

// X calls x.M().
//
// @Variant 0
// @Ensures True
func X(x sibi.J) (n int) {
	if x == nil {
		return 0
	}
	return x.M()
}
