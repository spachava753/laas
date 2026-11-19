// Package funcvaluesclient calls through values of a function type of
// another package, whose contract it reads from there.
package funcvaluesclient

import (
	"funcvalueslib"
	"funcvaluesunread"
)

// TwoSteps takes two steps.
//
// @Requires s != nil And 0 <= x <= 0
// @Ensures 0 <= y <= 200
func TwoSteps(s funcvalueslib.Step, x int) (y int) {
	y = s(x)
	return funcvalueslib.Run(s, y)
}

// TooFar takes a step from where the contract does not allow it.
//
// @Requires s != nil
// @Ensures True
func TooFar(s funcvalueslib.Step) (y int) {
	return s(funcvalueslib.Limit + 1) // want `vego: precondition of s may not hold: 0 <= x <= Limit`
}

// UsesUnread calls a value of a type whose package did not read all its
// annotations.
//
// @Requires op != nil
// @Ensures True
func UsesUnread(op funcvaluesunread.Op) (y int) {
	return op(1) // want `vego: the contract of Op cannot be used: the annotations of package funcvaluesunread were not all read` `cannot verify UsesUnread: the contract of Op could not be understood`
}
