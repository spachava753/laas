// Package manywrites writes one field through ten pointers. Its contract is
// true, and every clause of it should be proved. Seven are not: Z3 runs out
// of its resource limit on them, also when the pointers are required to
// differ; with five pointers the function verifies. In the same function
// with thirty pointers, the chain of tactics runs out in ctx-simplify at
// any limit; see The prover in the ROADMAP.
// When a change proves them, remove the expectations.
package manywrites

// P is a point.
type P struct{ x, y int }

// Set sets the x of ten points.
//
// @Requires p0 != nil And p1 != nil And p2 != nil And p3 != nil And p4 != nil And p5 != nil And p6 != nil And p7 != nil And p8 != nil And p9 != nil
// @Modifies p0.x, p1.x, p2.x, p3.x, p4.x, p5.x, p6.x, p7.x, p8.x, p9.x
// @Ensures p0.x' = 1 And p1.x' = 1 And p2.x' = 1 And p3.x' = 1 And p4.x' = 1 And p5.x' = 1 And p6.x' = 1 And p7.x' = 1 And p8.x' = 1 And p9.x' = 1
func Set(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9 *P) {
	p0.x = 1
	p1.x = 1
	p2.x = 1
	p3.x = 1
	p4.x = 1
	p5.x = 1
	p6.x = 1
	p7.x = 1
	p8.x = 1
	p9.x = 1
} // want `postcondition may not hold: p2.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p3.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p4.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p5.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p6.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p7.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p8.x' = 1 \(Z3 reached its resource limit`
