// Package addrtestonly takes the address of S.n only in its own test file,
// which vego reads as syntax, so the field is addressable (D6 and F9 of the
// review of step 1a of F42).
package addrtestonly

// S holds a number.
type S struct{ m, n int }

// Keep writes what q points to and claims s.n unchanged.
//
// @Requires q != nil And s != nil
// @Modifies q
// @Ensures s.n' = s.n
func Keep(q *int, s *S) {
	*q = 7
} // want `vego: postcondition may not hold: s\.n' = s\.n`
