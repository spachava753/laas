// Package varcode holds package-level variables of interface and function
// types (part 3 of package-level variables).
package varcode

import (
	"fmt"
	"io"
	"net/http"
	"os"
	"time"

	"varcodelib"
)

var stdout io.Writer = os.Stdout

// println writes through the variable, which it lists.
//
// @Requires |s| <= 100 And stdout != nil
// @Modifies stdout
// @Ensures True
func println(s string) {
	fmt.Fprintln(stdout, s)
}

// printUnlisted does not list it.
//
// @Requires stdout != nil
// @Ensures True
func printUnlisted() {
	stdout.Write([]byte("x")) // want `^vego: stdout.Write may modify the footprint of stdout, which printUnlisted may not modify; list it in a // @Modifies clause$`
}

// setOut replaces the writer.
//
// @Requires w != nil
// @Modifies stdout
// @Ensures stdout' = w
func setOut(w io.Writer) {
	stdout = w
}

// Clock reads the time.
//
// @Ensures True
type Clock func() (t time.Time)

var now Clock = time.Now

// stamp calls the hook a test may replace.
//
// @Ensures True
func stamp() (r bool) {
	if now == nil {
		return false
	}
	_ = now()
	return true
}

var kept http.ResponseWriter

// keep stores a writer, which outlives its request.
//
// @Modifies kept
// @Ensures True
func keep(w http.ResponseWriter) {
	kept = w // want `^vego: w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into kept`
}

var fired, other int

// Hook runs when something happens, and may count it.
//
// @Modifies fired
// @Ensures True
type Hook func()

// countFire counts.
//
// @Modifies fired
// @Ensures True
func countFire() {
	if fired < 1000 {
		fired++
	}
}

// fires claims fired kept across a call of h, whose type lists it; it
// lists other too, which the literal in writesOther, a value h may be,
// writes.
//
// @Requires h != nil
// @Modifies fired, other
// @Ensures r
func fires(h Hook) (r bool) {
	a := fired
	h()
	return a == fired // want `^vego: postcondition may not hold: r$`
}

// firesUnlisted does not list what h changes.
//
// @Requires h != nil
// @Ensures True
func firesUnlisted(h Hook) {
	h() // want `^vego: h may modify fired, which firesUnlisted may not modify; list it in a // @Modifies clause$`
}

// uses makes a Hook of countFire.
//
// @Modifies fired, other
// @Ensures True
func uses(n int) {
	_ = fires(countFire)
}

// writesOther makes a Hook of a literal that writes what the type does not
// list.
//
// @Modifies fired, other
// @Ensures True
func writesOther(n int) {
	_ = fires(func() { other = 1 }) // want `^vego: other is assigned, which Hook may not modify; the contract of Hook does not list it, so code that writes it cannot be used there, in the function literal used as a value of type Hook at varcode.go:\d+:\d+$`
}

// setsOther stores code of this package into a variable of another
// package, which would run it at times no contract describes.
//
// @Modifies varcodelib.OnEvent
// @Ensures True
func setsOther(n int) {
	varcodelib.OnEvent = func() {} // want `^vego: cannot verify setsOther: varcodelib.OnEvent is a variable of package varcodelib that holds code, and code of this package stored there would be run by that package at times no contract describes; keeping code to run later is not supported yet$`
}
