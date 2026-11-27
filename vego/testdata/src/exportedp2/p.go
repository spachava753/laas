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
func tick() { letoutq.Tick(0) } // want `this call may not end: tick calls letoutq\.Tick\(0\) at p.go:\d+:\d+, which may run Bump, Bump calls tick at p.go:\d+:\d+`

// Bump breaks the invariant around a call of tick.
//
// @Modifies count
// @Ensures True
func Bump() {
	count = total
	tick() // want `vego: invariant of count, total may not hold before the call to tick, which may assume it: count < total; it was not kept from entry, since count may have changed: the assignment to count at p\.go:27:2 may write it` `this call may not end: Bump calls tick at p.go:\d+:\d+, tick calls letoutq\.Tick\(0\) at p.go:\d+:\d+, which may run Bump`
	count = total - 1
}

// mid calls tick, two calls away from Tick.
//
// @Ensures True
func mid() { tick() } // want `this call may not end: mid calls tick at p.go:\d+:\d+, tick calls letoutq\.Tick\(0\) at p.go:\d+:\d+, which may run BumpDeep, BumpDeep calls mid at p.go:\d+:\d+`

// BumpDeep breaks the invariant around a call of mid, which reaches Tick
// through tick (F18 of the review of F10).
//
// @Modifies count
// @Ensures True
func BumpDeep() {
	count = total
	mid() // want `vego: invariant of count, total may not hold before the call to mid, which may assume it: count < total` `this call may not end: BumpDeep calls mid at p.go:\d+:\d+, mid calls tick at p.go:\d+:\d+, tick calls letoutq\.Tick\(0\) at p.go:\d+:\d+, which may run BumpDeep`
	count = total - 1
}
