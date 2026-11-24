// Package hiddenlook hands code of the package to a trusted function during
// initialisation, before the variable that code reads is initialised: Go's
// order does not follow the conversion to any (F23 of the review of step 7
// of F32).
package hiddenlook

import "hiddenlookq"

type hooker struct{}

// Init reads the table, and is not verified.
func (hooker) Init() { _ = third() }

var _ = hiddenlookq.Look(hooker{})

// buildTable makes a table of three.
//
// @Ensures |t| = 3
func buildTable() (t []int) {
	return []int{1, 2, 3}
}

var table = buildTable()

// third reads the table, which may not be initialised yet when Init runs it.
//
// @Ensures True
func third() (r int) {
	return table[2] // want `vego: cannot verify third: table is not known to have its value yet when this runs: hooker\{\} is handed to hiddenlookq.Look, which may call back into this package`
}
