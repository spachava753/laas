// Package letoutp stores its own code into memory of letoutq, which a
// call of letoutq may run while its invariant is broken. Before, Bump
// verified and check divided by zero at run time.
package letoutp

import "letoutq"

// @Invariant 0 <= count And count < total
var (
	count int
	total = 1
)

// check divides by what the invariant keeps positive.
//
// @Ensures True
func check() { _ = 10 / (total - count) }

// Install stores check into what it is handed, which letoutq made.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func Install(b *letoutq.Box) { b.H = check }

// Bump breaks the invariant around a call of letoutq.Tick, which may run
// check.
//
// @Modifies count
// @Ensures True
func Bump() {
	count = total
	letoutq.Tick(0) // want `^vego: invariant of count, total may not hold before the call to Tick, which may assume it: count < total; it was not kept from entry, since count may have changed: the assignment to count at p.go:\d+:\d+ may write it$` `this call may not end: Bump calls letoutq.Tick\(0\) at p.go:\d+:\d+, which may run Bump; Tick reads a package-level variable that can hold code`
	count = total - 1
}
