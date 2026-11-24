package varcode

import (
	"flag"
	"io"
	"os"
)

// Positive returns a positive number.
//
// @Ensures r > 0
type Positive func() (r int)

// The initialiser of a variable of a type with a contract is held to the
// contract where it is declared: getBad's breaks it, getGood's keeps it.
var getBad Positive = func() (r int) { return -1 } // want `^vego: postcondition may not hold: r > 0, in the function literal used as a value of type Positive at inits.go:\d+:\d+$`

var getGood Positive = func() (r int) { return 1 }

// setGets makes both assigned.
//
// @Modifies getBad, getGood
// @Ensures True
func setGets() {
	getBad, getGood = one, one
}

// one returns one.
//
// @Ensures r > 0
func one() (r int) { return 1 }

// useGets relies on the contract of Positive for both.
//
// @Ensures r > 0
func useGets() (r int) {
	if getBad == nil || getGood == nil {
		return 1
	}
	_ = getGood()
	return getBad()
}

// bad claims to have written more than it was handed, and is not verified.
type bad struct{}

func (bad) Write(p []byte) (int, error) { return len(p) + 5, nil }

// The initialiser of an interface variable is converted where it is
// declared, and a method with no contract cannot stand behind io.Writer.
var wBad io.Writer = bad{} // want `^vego: cannot verify the initialiser of wBad: it uses Write as a method of io.Writer, and Write has no contract`

var wGood io.Writer = os.Stdout

// setWs makes both assigned.
//
// @Requires x != nil
// @Modifies wBad, wGood
// @Ensures True
func setWs(x io.Writer) {
	wBad, wGood = x, x
}

// usage would be run by package flag at times no contract describes.
func usage() {}

// setUsage stores code of this package into flag.Usage.
//
// @Ensures True
func setUsage() {
	flag.Usage = usage // want `^vego: cannot verify setUsage: flag.Usage is a variable of package flag that holds code, and code of this package stored there would be run by that package at times no contract describes; keeping code to run later is not supported yet$`
}

// two returns the standard output and a number.
//
// @Ensures n = 1
func two() (w *os.File, n int) { return os.Stdout, 1 }

// pick returns w.
//
// @Ensures r = w
func pick(w io.Writer, n int) (r io.Writer) { return w }

// The conversion of the first result of two to io.Writer has no
// expression of its own, so nothing would check it.
var wMulti io.Writer = pick(two()) // want `^vego: cannot verify the initialiser of wMulti: Go converts a value to an interface type in the initialiser of wMulti, and which expression it converts could not be told`

// twoPositive is not verified, and what it returns breaks the contract.
func twoPositive() (a, b Positive) { return func() int { return -1 }, one }

// Variables given one call with several results, which no expression of
// their own makes.
var pa, pb Positive = twoPositive() // want `^vego: cannot verify the initialiser of pa: pa is given one result of a call with several`

// setMore makes them assigned.
//
// @Requires w != nil
// @Modifies wMulti, pa, pb
// @Ensures True
func setMore(w io.Writer) {
	wMulti, pa, pb = w, one, one
}
