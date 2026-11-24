// Package initcallslib exports fixed variables whose initialisers call
// functions, and publishes what their runs show (step 5b of F32).
package initcallslib

import "regexp"

// buildTable makes a table of three.
//
// @Ensures |t| = 3
func buildTable() (t []int) {
	return []int{1, 2, 3}
}

// Table has three elements.
var Table = buildTable()

// Word matches words.
var Word = regexp.MustCompile("^[a-z]+$")

// mk returns its argument.
//
// @Ensures r = k
func mk(k int) (r int) { return k }

// Seven is seven.
var Seven = mk(7)
