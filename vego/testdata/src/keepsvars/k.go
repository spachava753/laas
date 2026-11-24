// Package keepsvars keeps an assigned variable across a call of a function
// that never assigns it (S1 of F31's coder, built in F32).
package keepsvars

import (
	"fmt"
	"io"
)

var counts = map[string]int{}

// bump writes into the map and never assigns counts.
//
// @Requires counts != nil
// @Modifies counts
// @Ensures True
func bump() { counts["a"] = 1 }

// bumpTwice writes after bump, into the same map.
//
// @Requires counts != nil
// @Modifies counts
// @Ensures True
func bumpTwice() {
	bump()
	counts["b"] = 2
}

// Resetter may give counts a new map, by its contract.
//
// @Modifies counts
// @Ensures True
type Resetter func()

// viaValue calls r, which may assign counts.
//
// @Requires r != nil
// @Modifies counts
// @Ensures True
func viaValue(r Resetter) { r() }

// afterValue writes after viaValue.
//
// @Requires r != nil And counts != nil
// @Modifies counts
// @Ensures True
func afterValue(r Resetter) {
	viaValue(r)
	counts["c"] = 3 // want `vego: map may be nil` `vego: counts\["c"\] is assigned, which afterValue may not modify`
}

// deferred assigns counts in a deferred literal.
//
// @Modifies counts
// @Ensures counts' != nil
func deferred() {
	defer func() { counts = map[string]int{} }()
}

// afterDeferred writes after deferred.
//
// @Requires counts != nil
// @Modifies counts
// @Ensures True
func afterDeferred() {
	deferred()
	counts["d"] = 4 // want `vego: counts\["d"\] is assigned, which afterDeferred may not modify`
}

// renew assigns counts.
//
// @Modifies counts
// @Ensures counts' != nil
func renew() { counts = map[string]int{} }

// viaHelper calls renew.
//
// @Modifies counts
// @Ensures counts' != nil
func viaHelper() { renew() }

// afterHelper writes after viaHelper.
//
// @Requires counts != nil
// @Modifies counts
// @Ensures True
func afterHelper() {
	viaHelper()
	counts["e"] = 5 // want `vego: counts\["e"\] is assigned, which afterHelper may not modify`
}

var out io.Writer

// setOut makes out assigned.
//
// @Requires w != nil
// @Modifies out
// @Ensures out' = w
func setOut(w io.Writer) { out = w }

// printLine writes through out, never assigns it, and says nothing of it.
//
// @Requires out != nil And |s| <= 100
// @Modifies out
// @Ensures True
func printLine(s string) {
	fmt.Fprintln(out, s)
}

// printTwice calls printLine twice: out still holds the writer it held on
// entry at the second call, which the separation of printLine needs.
//
// @Requires out != nil And |s| <= 100
// @Modifies out
// @Ensures True
func printTwice(s string) {
	printLine(s)
	printLine(s)
}
