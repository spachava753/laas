// Package manywrites writes one field through thirty pointers. Its contract
// is true, and every clause of it should be proved. At the default limit 29
// are not, and at ten times the limit 29 are still not, also when the
// pointers are required to differ; at 400000000 one of them stops in the
// ctx-simplify of the chain of tactics, which the chain without it proves.
// With five pointers the function verifies, and with ten it needs
// -vego.rlimit=40000000. See The prover in the ROADMAP. When a change
// proves these clauses, remove the expectations.
package manywrites

// P is a point.
type P struct{ x, y int }

// Set sets the x of thirty points.
//
// @Requires p0 != nil And p1 != nil And p2 != nil And p3 != nil And p4 != nil And p5 != nil And p6 != nil And p7 != nil And p8 != nil And p9 != nil And p10 != nil And p11 != nil And p12 != nil And p13 != nil And p14 != nil And p15 != nil And p16 != nil And p17 != nil And p18 != nil And p19 != nil And p20 != nil And p21 != nil And p22 != nil And p23 != nil And p24 != nil And p25 != nil And p26 != nil And p27 != nil And p28 != nil And p29 != nil
// @Modifies p0.x, p1.x, p2.x, p3.x, p4.x, p5.x, p6.x, p7.x, p8.x, p9.x, p10.x, p11.x, p12.x, p13.x, p14.x, p15.x, p16.x, p17.x, p18.x, p19.x, p20.x, p21.x, p22.x, p23.x, p24.x, p25.x, p26.x, p27.x, p28.x, p29.x
// @Ensures p0.x' = 1 And p1.x' = 1 And p2.x' = 1 And p3.x' = 1 And p4.x' = 1 And p5.x' = 1 And p6.x' = 1 And p7.x' = 1 And p8.x' = 1 And p9.x' = 1 And p10.x' = 1 And p11.x' = 1 And p12.x' = 1 And p13.x' = 1 And p14.x' = 1 And p15.x' = 1 And p16.x' = 1 And p17.x' = 1 And p18.x' = 1 And p19.x' = 1 And p20.x' = 1 And p21.x' = 1 And p22.x' = 1 And p23.x' = 1 And p24.x' = 1 And p25.x' = 1 And p26.x' = 1 And p27.x' = 1 And p28.x' = 1 And p29.x' = 1
func Set(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29 *P) {
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
	p10.x = 1
	p11.x = 1
	p12.x = 1
	p13.x = 1
	p14.x = 1
	p15.x = 1
	p16.x = 1
	p17.x = 1
	p18.x = 1
	p19.x = 1
	p20.x = 1
	p21.x = 1
	p22.x = 1
	p23.x = 1
	p24.x = 1
	p25.x = 1
	p26.x = 1
	p27.x = 1
	p28.x = 1
	p29.x = 1
} // want `postcondition may not hold: p0.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p1.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p2.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p3.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p4.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p5.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p6.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p7.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p8.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p9.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p10.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p11.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p12.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p13.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p14.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p15.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p16.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p17.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p18.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p19.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p20.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p21.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p22.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p23.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p24.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p25.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p26.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p27.x' = 1 \(Z3 reached its resource limit` `postcondition may not hold: p28.x' = 1 \(Z3 reached its resource limit`
