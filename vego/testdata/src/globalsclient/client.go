// Package globalsclient reads the package-level variables of globalslib.
package globalsclient

import "globalslib"

// Limit reads a variable of another package.
//
// @Ensures r = 5 And r = globalslib.Limit
func Limit() (r int) { return globalslib.Limit }

// Names reads the length of a slice of another package.
//
// @Ensures r = 2
func Names() (r int) { return len(globalslib.Names) }

// Origin reads a struct of another package.
//
// @Ensures r = 3
func Origin() (r int) { return globalslib.Origin.X + globalslib.Origin.Y }

// Hidden relies on a contract that names a variable this package cannot
// name.
//
// @Ensures r = 7
func Hidden() (r int) { return globalslib.Hidden() }

// AtLimit meets a Requires that names a variable of another package.
//
// @Ensures r = 2
func AtLimit() (r int) { return globalslib.AtLimit(3) }

// OverLimit does not.
//
// @Ensures True
func OverLimit() (r int) {
	return globalslib.AtLimit(6) // want `vego: precondition of AtLimit may not hold: 0 <= n <= Limit`
}

// Counter reads a variable its package changes.
//
// @Ensures True
func Counter() (r int) {
	return globalslib.Counter // want `vego: cannot verify Counter: globalslib.Counter is assigned at lib.go:24 in package globalslib; package-level variables that are changed are not supported yet`
}

// Beside calls a function of another package whose contract reads memory
// through a package-level variable beside an append.
//
// @Requires |u| = 2 And |t| = 1
// @Modifies u, t
func Beside(u [][]int, t []int) {
	u[globalslib.First()&1] = append(t[:0], 5) // want `vego: cannot verify Beside: First is called in the target of this assignment, and Go may call it before or after append writes into the array of t\[:0\]; assign the result of First to a variable in a statement of its own first`
}
