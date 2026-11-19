// Package toolarge holds a program whose formulas grow faster than its
// text, on purpose: the verifier must refuse it rather than use memory
// without bound. The tests run it without the check that fails on such
// growth, since here the growth is what the program is for.
package toolarge

// Doubles builds a number whose formula, written out, doubles in size with
// each statement. The verifier refuses it before it grows without bound.
//
// @Requires 0 <= x <= 1
// @Ensures True
func Doubles(x int) (result int) { // want `vego: cannot verify Doubles: a formula built to verify it has grown beyond 1048576 nodes, which is the limit; split the function, or the expressions in it, into smaller ones`
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	x = x + x
	return x
}
