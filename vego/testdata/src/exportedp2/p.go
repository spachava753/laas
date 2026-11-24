// Package exportedp2 is exportedp with the call of Tick moved into a helper.
package exportedp2

import "letoutq"

// @Invariant 0 <= count And count < total
var (
	count int
	total = 1
)

// Check divides by what the invariant keeps positive.
//
// @Ensures True
func Check() { _ = 10 / (total - count) }

// tick calls Tick, and touches nothing of the group.
//
// @Ensures True
func tick() { letoutq.Tick(0) }

// Bump breaks the invariant around a call of tick.
//
// @Modifies count
// @Ensures True
func Bump() {
	count = total
	tick() // want `vego: invariant of count, total may not hold before the call to tick, which may assume it: count < total; it was not kept from entry, since count may have changed: the assignment to count at p\.go:27:2 may write it`
	count = total - 1
}
