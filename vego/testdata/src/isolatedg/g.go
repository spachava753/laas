// Package isolatedg breaks the invariant of a group around calls of
// trusted functions. A call of one whose entry is isolated and that is
// handed no code reaches no code of the package; any other call into
// another package may reach the exported Check (F11 of the review of the
// design of F32).
package isolatedg

import (
	"fmt"
	"log"
	"strings"

	"isolatedq"
)

// @Invariant 0 <= count And count < total
var (
	count int
	total = 1
)

// Check divides by what the invariant keeps positive.
//
// @Ensures True
func Check() { _ = 10 / (total - count) }

// Upper calls strings.ToUpper while the invariant is broken, which runs
// nothing of the package.
//
// @Requires |s| <= 100
// @Modifies count
// @Ensures True
func Upper(s string) (r string) {
	count = total
	r = strings.ToUpper(s)
	count = total - 1
	return r
}

// Logs calls log.Print while the invariant is broken; the standard logger
// writes to what code that is not verified set, which may be a writer of
// this package.
//
// @Modifies count
// @Ensures True
func Logs() {
	count = total
	log.Print("x") // want `vego: invariant of count, total may not hold before the call to Print, which may assume it: count < total`
	count = total - 1
}

var errCheck = fmt.Errorf("check")

// Formats hands fmt an error, whose methods fmt runs.
//
// @Modifies count
// @Ensures True
func Formats() (r string) {
	count = total
	r = fmt.Sprint(errCheck) // want `vego: invariant of count, total may not hold before the call to Sprint, which may assume it: count < total`
	count = total - 1
	return r
}

// Hands hands an isolated entry of the project a box that holds a
// function, which it may run.
//
// @Requires b != nil
// @Modifies count
// @Ensures True
func Hands(b *isolatedq.Box) {
	count = total
	isolatedq.Hand(b) // want `vego: invariant of count, total may not hold before the call to Hand, which may assume it: count < total`
	count = total - 1
}

// Plain hands it a box that holds no code.
//
// @Requires b != nil
// @Modifies count
// @Ensures True
func Plain(b *isolatedq.Plain) {
	count = total
	isolatedq.Look(b)
	count = total - 1
}
