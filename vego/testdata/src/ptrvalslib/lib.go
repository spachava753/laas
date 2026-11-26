// Package ptrvalslib increments what a pointer points to, for a caller in
// another package: one box per type for every package and verifier (F1 of
// the design review of F37).
package ptrvalslib

// Inc increments what p points to.
//
// @Requires p != nil And *p < 1000
// @Modifies p
// @Ensures *p' = *p + 1
func Inc(p *int) {
	*p = *p + 1
}
