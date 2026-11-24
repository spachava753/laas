// Package globalsvalues holds calls through values that may run code of the
// package which writes its variables.
package globalsvalues

import "io"

// A call through a value may run code of the package, which the call graph
// finds; what that code writes is a target of the call, which the caller
// forgets and must cover (F7 of the design review, F17 of the review of
// step 2). Before, Call and Direct verified, and Twice and Around were
// proved and false at run time.

var bumps int

// Bump is exported and not verified, so a value of type Fire may be it.
func Bump(n int) {
	if bumps < 1000 {
		bumps += n
	}
}

// Fire is a function a caller hands over.
//
// @Ensures True
type Fire func(n int)

// Call calls f and does not list what f may write.
//
// @Requires f != nil
// @Ensures True
func Call(f Fire) {
	f(1) // want `^vego: f may modify bumps, which Call may not modify; code of this package that the call may run writes it; list it in a // @Modifies clause$`
}

// CallListed lists it.
//
// @Requires f != nil
// @Modifies bumps
// @Ensures True
func CallListed(f Fire) {
	f(1)
}

// Twice claims bumps is the same around a call that may run Bump.
//
// @Requires f != nil
// @Modifies bumps
// @Ensures r
func Twice(f Fire) (r bool) {
	a := bumps
	CallListed(f)
	return bumps == a // want `^vego: postcondition may not hold: r$`
}

// Direct claims the same around the call itself.
//
// @Requires f != nil
// @Modifies bumps
// @Ensures r
func Direct(f Fire) (r bool) {
	a := bumps
	f(1)
	return bumps == a // want `^vego: postcondition may not hold: r$`
}

var written int

type countingWriter struct{}

// Write counts, and is not verified.
func (countingWriter) Write(p []byte) (int, error) {
	written++
	return len(p), nil
}

// Around claims written is the same around a write through w, which may be
// a countingWriter.
//
// @Requires w != nil
// @Modifies w, written
// @Ensures r
func Around(w io.Writer) (r bool) {
	a := written
	w.Write([]byte("x"))
	return written == a // want `^vego: postcondition may not hold: r$`
}

// AroundListed lists what the writer may change and claims nothing of it.
//
// @Requires w != nil
// @Modifies w, written
// @Ensures True
func AroundListed(w io.Writer) {
	w.Write([]byte("x"))
}

// AroundUnlisted does not list it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func AroundUnlisted(w io.Writer) {
	w.Write([]byte("x")) // want `^vego: w.Write may modify written, which AroundUnlisted may not modify; code of this package that the call may run writes it; list it in a // @Modifies clause$`
}
