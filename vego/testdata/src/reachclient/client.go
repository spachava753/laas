// Package reachclient reads reachlib.Count around calls through values
// that may run its writers, which call reachlib.
package reachclient

import (
	"io"

	"reachlib"
)

type plain struct{}

// Write calls a function of reachlib that is not verified.
func (plain) Write(p []byte) (int, error) {
	reachlib.Inc()
	return len(p), nil
}

type viaVerified struct{}

// Write calls a verified function of reachlib.
func (viaVerified) Write(p []byte) (int, error) {
	reachlib.IncV()
	return len(p), nil
}

// Around claims Count is the same around a write through w. Before, it
// verified, and was false for both writers.
//
// @Requires w != nil
// @Modifies w
// @Ensures r
func Around(w io.Writer) (r bool) {
	a := reachlib.Count
	w.Write([]byte("x")) // want `^vego: w.Write may modify the state of package reachlib \(reachlib.Count\), which Around may not modify; list reachlib in a // @Modifies clause$`
	return reachlib.Count == a
}

// AroundListed lists the state of reachlib and forgets Count.
//
// @Requires w != nil
// @Modifies w, reachlib
// @Ensures r
func AroundListed(w io.Writer) (r bool) {
	a := reachlib.Count
	w.Write([]byte("x"))
	return reachlib.Count == a // want `^vego: postcondition may not hold: r$`
}

// Hook is a function a caller hands over.
//
// @Ensures True
type Hook func()

// tick is verified and lists the state of reachlib.
//
// @Modifies reachlib
// @Ensures True
func tick() { reachlib.IncV() }

var _ Hook = tick

// Fires claims Count is the same around a call that may run tick.
//
// @Requires f != nil
// @Modifies reachlib
// @Ensures r
func Fires(f Hook) (r bool) {
	a := reachlib.Count
	f()
	return reachlib.Count == a // want `^vego: postcondition may not hold: r$`
}

// Tock is a function of one number a caller hands over.
//
// @Ensures True
type Tock func(n int)

// tock is verified and names a variable of reachlib.
//
// @Modifies reachlib.Count
// @Ensures True
func tock(n int) { reachlib.IncV() }

var _ Tock = tock

// FiresTock claims Count kept across a call that may run tock.
//
// @Requires f != nil
// @Modifies reachlib.Count
// @Ensures r
func FiresTock(f Tock) (r bool) {
	a := reachlib.Count
	f(1)
	return reachlib.Count == a // want `^vego: postcondition may not hold: r$`
}
