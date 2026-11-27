// Package sibhp hands sibhq.F the value it holds; it imports neither sibhr
// nor anything that does (F13 of the review of the table of F43). Code that
// is not verified may hand G a sibhr.T that wraps a PT: sibhq.F calls M,
// which is T.M, which calls N, which is PT.N, which calls G. The base found
// the cycle by the strict reading of x, which reaches everything; since F43
// the call reaches what sibhq.F runs (M), and nobody sees T.M's N. It is
// the limit "What a proof assumes" states, which carries the narrowing of
// an interface operand by a summary. Verified code that wires them is
// refused, since PT converted to sibhi.I is stratified.
package sibhp

import (
	"cycles/held/sibhi"
	"cycles/held/sibhq"
)

// PT calls G back.
type PT struct{ J sibhi.J }

// N calls G.
//
// @Requires t != nil
// @Variant 1
// @Ensures True
func (t *PT) N() (n int) { return G(t.J) }

// G hands x to sibhq.F.
//
// @Variant 0
// @Ensures True
func G(x sibhi.J) (n int) { return sibhq.F(x) }
