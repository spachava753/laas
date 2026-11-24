package varcode

import (
	"context"
	"flag"
	"io"
	"os"

	"varcodelib"
)

// Positive returns a positive number.
//
// @Ensures r > 0
type Positive func() (r int)

// The initialiser of a variable of a type with a contract is held to the
// contract, and a read of the variable in verified code relies on it:
// getBad's breaks it, getGood's keeps it. What is wrong with an initialiser
// is reported at the reads, not where the variable is declared, which
// nothing may read.
var getBad Positive = func() (r int) { return -1 }

var getGood Positive = func() (r int) { return 1 }

// setGets makes both assigned, and reads neither.
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

// useBad relies on the contract of Positive for getBad.
//
// @Ensures r > 0
func useBad() (r int) {
	if getBad == nil { // want `^vego: cannot verify useBad: getBad cannot be relied on: its initialiser does not verify, at inits.go:\d+:\d+: postcondition may not hold: r > 0, in the function literal used as a value of type Positive at inits.go:\d+:\d+$`
		return 1
	}
	return getBad()
}

// useGood relies on it for getGood.
//
// @Ensures r > 0
func useGood() (r int) {
	if getGood == nil {
		return 1
	}
	return getGood()
}

// bad claims to have written more than it was handed, and is not verified.
type bad struct{}

func (bad) Write(p []byte) (int, error) { return len(p) + 5, nil }

// The initialiser of an interface variable converts its value, and a
// method with no contract cannot stand behind io.Writer.
var wBad io.Writer = bad{}

var wGood io.Writer = os.Stdout

// setWs makes both assigned.
//
// @Requires x != nil
// @Modifies wBad, wGood
// @Ensures True
func setWs(x io.Writer) {
	wBad, wGood = x, x
}

// writeBad writes through wBad.
//
// @Requires wBad != nil
// @Modifies wBad
// @Ensures True
func writeBad() {
	wBad.Write([]byte("x")) // want `^vego: cannot verify writeBad: wBad cannot be relied on: its initialiser does not verify, at inits.go:\d+:\d+: it uses Write as a method of io.Writer, and Write has no contract`
}

// writeGood writes through wGood.
//
// @Requires wGood != nil
// @Modifies wGood
// @Ensures True
func writeGood() {
	wGood.Write([]byte("x"))
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
var wMulti io.Writer = pick(two())

// twoPositive is not verified, and what it returns breaks the contract.
func twoPositive() (a, b Positive) { return func() int { return -1 }, one }

// Variables given one call with several results, which no expression of
// their own makes.
var pa, pb Positive = twoPositive()

// setMore makes them assigned.
//
// @Requires w != nil
// @Modifies wMulti, pa, pb
// @Ensures True
func setMore(w io.Writer) {
	wMulti, pa, pb = w, one, one
}

// readMore reads them.
//
// @Ensures r
func readMore() (r bool) {
	_ = wMulti != nil // want `^vego: cannot verify readMore: wMulti cannot be relied on: its initialiser does not verify, at inits.go:\d+:\d+: Go converts a value to an interface type in the initialiser of wMulti, and which expression it converts could not be told`
	return pb != nil || true
}

// readPb reads pb.
//
// @Ensures r
func readPb() (r bool) {
	return pb != nil || true // want `^vego: cannot verify readPb: pb cannot be relied on: its initialiser does not verify, at inits.go:\d+:\d+: pb is given one result of a call with several`
}

// A fixed variable whose initialiser calls a function with no contract,
// which nothing here reads, is not reported.
var background = context.Background()

// readLibRoot reads a variable of another package whose initialiser does
// not verify, which that package publishes.
//
// @Ensures r
func readLibRoot() (r bool) {
	return varcodelib.Root != nil || true // want `^vego: cannot verify readLibRoot: varcodelib.Root cannot be relied on: its initialiser does not verify, at lib.go:\d+:\d+: it calls Background, which has no contract`
}

// readLibStarted reads one whose initialiser verifies.
//
// @Ensures r
func readLibStarted() (r bool) {
	return varcodelib.Started != nil || true
}
