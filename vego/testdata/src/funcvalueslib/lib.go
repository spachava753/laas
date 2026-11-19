// Package funcvalueslib declares function types with contracts that other
// packages use.
package funcvalueslib

import "errors"

const Limit = 100

// Step moves a number up by at most Limit.
//
// @Requires 0 <= x <= Limit
// @Ensures x <= y <= x + Limit
type Step func(x int) (y int)

// Run takes one step, through the value it is given.
//
// @Requires s != nil And 0 <= x <= Limit
// @Ensures x <= y <= x + Limit
func Run(s Step, x int) (y int) {
	return s(x)
}

// Count counts, and calls nothing through a value.
//
// @Requires 0 <= n < 1000
// @Ensures m = n + 1
func Count(n int) (m int) {
	return n + 1
}

// ErrStop is what a stop returns.
var ErrStop = errors.New("stop")

// Stop fails with ErrStop of this package.
//
// @Ensures err = nil Or err = ErrStop
type Stop func() (err error)
