// Package funcvaluesclient calls through values of a function type of
// another package, whose contract it reads from there.
package funcvaluesclient

import (
	"errors"

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
	return op(1) // want `vego: the contract of Op cannot be used: the annotations of package funcvaluesunread were not all read`
}

// Each caller of a function of another package that calls through a value
// may make such a call too, whichever is looked at first.

// idStep takes a step of nothing.
//
// @Requires 0 <= x <= 100
// @Ensures x <= y <= x + 100
func idStep(x int) (y int) {
	return x
}

// viaRunA takes a step through Run.
//
// @Requires 0 <= x <= 100
// @Ensures x <= y <= x + 100
func viaRunA(x int) (y int) {
	return funcvalueslib.Run(idStep, x)
}

// viaRunB takes a step through Run too.
//
// @Requires 0 <= x <= 100
// @Ensures x <= y <= x + 100
func viaRunB(x int) (y int) {
	return funcvalueslib.Run(idStep, x)
}

// BothA uses viaRunA as a value.
//
// @Ensures s != nil
func BothA() (s funcvalueslib.Step) {
	return viaRunA // want `vego: cannot verify BothA: viaRunA may call through a function value`
}

// BothB uses viaRunB as a value.
//
// @Ensures s != nil
func BothB() (s funcvalueslib.Step) {
	return viaRunB // want `vego: cannot verify BothB: viaRunB may call through a function value`
}

// First hands a step on to Run.
//
// @Requires s != nil
// @Ensures True
func First(s funcvalueslib.Step) (r int) {
	return funcvalueslib.Run(s, 1)
}

// helper takes a step by looping back through loop, which hands helper to
// Run: helper(5) calls loop(4), which calls helper(5) again through Run.
//
// @Requires 0 <= x <= 100
// @Variant x
// @Ensures x <= y <= x + 100
func helper(x int) (y int) {
	if x == 0 {
		return 0
	}
	loop(x - 1) // want `this call may not end: helper calls loop at client.go:\d+:\d+, loop hands helper to funcvalueslib.Run\(helper, x \+ 1\) at client.go:\d+:\d+, which may run helper`
	return x
}

// loop hands helper to Run.
//
// @Requires 0 <= x <= 99
// @Variant x
// @Ensures True
func loop(x int) (r int) {
	return funcvalueslib.Run(helper, x+1) // want `vego: cannot verify loop: helper may call through a function value`
}

// ErrStop is an error of this package with the name of the one that the
// contract of funcvalueslib.Stop names.
var ErrStop = errors.New("mine")

// A literal made into a value of a type of another package is checked
// against the contract as it was written there: ErrStop is the error of
// funcvalueslib. Before, it was read in this file, and this verified.
//
// @Ensures s != nil
func WrongStop() (s funcvalueslib.Stop) {
	return func() error { return ErrStop } // want `postcondition may not hold: err = nil Or err = ErrStop, in the function literal used as a value of type Stop`
}

// @Ensures s != nil
func RightStop() (s funcvalueslib.Stop) {
	return func() error { return funcvalueslib.ErrStop }
}
