// Package ptrgloballib has a package-level number whose address no code of
// the package takes, and a proof that relies on that (F42).
package ptrgloballib

// N is a number of the package.
var N int

// Reset sets N.
//
// @Modifies N
// @Ensures N' = 0
func Reset() {
	N = 0
}

// F sets what p points to, and claims N unchanged, which holds while no
// pointer can point to N.
//
// @Requires p != nil
// @Modifies p
// @Ensures N' = N
func F(p *int) {
	*p = 5
}
