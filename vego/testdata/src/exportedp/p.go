// Package exportedp has an exported function that relies on an invariant,
// which another package can keep as a value and run later (F33 of the
// review of step 2 of part 2 of package-level variables).
package exportedp

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

// Bump breaks the invariant around a call of letoutq.Tick, which may run
// Check if another package stored it there.
//
// @Modifies count
// @Ensures True
func Bump() {
	count = total
	letoutq.Tick(0) // want `^vego: invariant of count, total may not hold before the call to Tick, which may assume it: count < total; it was not kept from entry, since count may have changed: the assignment to count at p.go:\d+:\d+ may write it$` `this call may not end: Bump calls letoutq\.Tick\(0\) at p.go:\d+:\d+, which may run Bump`
	count = total - 1
}
