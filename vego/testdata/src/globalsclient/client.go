// Package globalsclient reads the package-level variables of globalslib.
package globalsclient

import (
	"io"
	"log"

	"globalslib"
)

// Limit reads a variable of another package.
//
// @Ensures r = 5 And r = globalslib.Limit
func Limit() (r int) { return globalslib.Limit }

// Names reads the length of a slice of another package.
//
// @Ensures r = 2
func Names() (r int) { return len(globalslib.Names) }

// Origin reads a struct of another package.
//
// @Ensures r = 3
func Origin() (r int) { return globalslib.Origin.X + globalslib.Origin.Y }

// Hidden relies on a contract that names a variable this package cannot
// name.
//
// @Ensures r = 7
func Hidden() (r int) { return globalslib.Hidden() }

// AtLimit meets a Requires that names a variable of another package.
//
// @Ensures r = 2
func AtLimit() (r int) { return globalslib.AtLimit(3) }

// OverLimit does not.
//
// @Ensures True
func OverLimit() (r int) {
	return globalslib.AtLimit(6) // want `vego: precondition of AtLimit may not hold: 0 <= n <= Limit`
}

// Counter reads a variable its package changes.
//
// @Ensures True
func Counter() (r int) {
	return globalslib.Counter
}

// Beside calls a function of another package whose contract reads memory
// through a package-level variable beside an append.
//
// @Requires |u| = 2 And |t| = 1
// @Modifies u, t
func Beside(u [][]int, t []int) {
	u[globalslib.First()&1] = append(t[:0], 5) // want `vego: cannot verify Beside: First is called in the target of this assignment, and Go may call it before or after append writes into the array of t\[:0\]; assign the result of First to a variable in a statement of its own first`
}

// Pro reads a map of another package that is only read in its build.
//
// @Ensures r = 1000
func Pro() (r int) { return globalslib.Plans["pro"] }

// ListsVariable names a variable of another package in Modifies.
//
// @Modifies globalslib.Limit // want `vego: in Modifies annotation: globalslib.Limit is a package-level variable that nothing changes, and what it holds refers to no memory, so there is nothing to modify`
func ListsVariable() {}

// tally and logger are arranged by two initialisers: the logger holds a
// writer that writes what tally points to.
var tally = &globalslib.Tally{}

var logger = log.New(tally, "", 0)

// Quiet would hold if logging wrote nothing a caller can see.
//
// @Ensures r
func Quiet() (r bool) {
	n := tally.N
	if logger != nil { // want `vego: cannot verify Quiet: logger cannot be relied on: its initialiser does not verify, at client.go:\d+:\d+: it uses Write as a method of io.Writer, and Write has no co`
		logger.Printf("x")
	}
	return tally.N == n
}

// KeepTally keeps p across a write through w.
//
// @Requires p != nil And w != nil
// @Modifies w
// @Ensures r
func KeepTally(w io.Writer, p *globalslib.Tally) (r bool) {
	a := p.N
	w.Write([]byte("x"))
	return p.N == a
}

// HandsSink hands KeepTally a variable of another package beside its
// writer. Before F31 it verified, and KeepTally returned false through
// SinkTwice (F14 of the review of step 1 of F31).
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func HandsSink(w io.Writer) (r bool) {
	return KeepTally(w, globalslib.Sink) // want `^vego: the footprint of what is passed to KeepTally as w may hold memory that what is passed as globalslib.Sink reaches, and KeepTally relies on it not doing so: it is read from the package-level variable globalslib.Sink, and code elsewhere may hold a reference to what it refers to; take it as a parameter instead$`
}

// SinkTwice hands HandsSink the variable's memory as the writer, and is
// not verified.
func SinkTwice() bool { return HandsSink(globalslib.Sink) }
