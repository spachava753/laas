// Package sourcecallsclient hands a function of another package a literal
// under the contract its Calls gives.
package sourcecallsclient

import "sourcecallslib"

// Index reads a table at what Each hands its literal.
//
// @Requires |table| = 100 And Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func Index(xs []int, table []int) {
	sourcecallslib.Each(xs, func(x int) { _ = table[x] })
}

// Writes writes, in a run, the array Each is handed beside f.
//
// @Requires |xs| > 0 And Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Modifies xs
// @Ensures True
func Writes(xs []int) {
	sourcecallslib.Each(xs, func(x int) { xs[0] = x }) // want `xs\[0\] is assigned, which may be what an argument of sourcecallslib.Each refers to directly`
}
