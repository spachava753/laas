// r27b: a function of the package in a struct of another package, held in an any parameter.
package p

import "cycles/r27b/q"

// @Ensures True
func F(x any) (n int) {
	return q.Run(x) // want `this\ call\ may\ not\ end:\ F\ hands\ x\ to\ q\.Run\(x\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ F`
}

// h is not verified; it calls F.
func h() int { return F(q.Box{F: h}) }
