package closures

import (
	"errors"
	"fmt"
)

// ChangesAfter claims the result the return set, which a deferred literal
// changes.
//
// @Ensures result = 1
func ChangesAfter() (result int) {
	defer func() { result = 2 }()
	return 1 // want `vego: postcondition may not hold: result = 1`
}

// OverflowsLater increments a result without a bound in a deferred literal.
//
// @Ensures True
func OverflowsLater(x int) (result int) {
	defer func() { result++ }() // want `vego: addition may overflow int, in the function literal deferred at deferreddefects.go:21:8 and run at the return at deferreddefects.go:22:2`
	return x
}

// WritesUnlistedLater writes, in a deferred literal, memory its Modifies
// clause does not list.
//
// @Requires g != nil
// @Ensures True
func WritesUnlistedLater(g *Gauge) {
	defer func() { g.v = 1 }() // want `vego: g.v is assigned, which WritesUnlistedLater may not modify; list it in a // @Modifies clause, as g\.v, in the function literal deferred at deferreddefects.go:31:8 and run at the end of the function at deferreddefects.go:32:1`
}

// DefersInLoop puts off a literal in every iteration of a loop.
//
// @Requires g != nil And 0 <= n <= 3
// @Modifies g.v
func DefersInLoop(g *Gauge, n int) {
	// @Invariant 0 <= i <= n
	for i := range n {
		defer func() { g.Set(i) }() // want `vego: cannot verify DefersInLoop: defer inside a loop is not supported: how many calls it puts off is not known`
	}
}

// DefersRecover puts off recover.
//
// @Ensures True
func DefersRecover() {
	defer recover() // want `vego: cannot verify DefersRecover: recover is not supported`
}

// RecoversLater calls recover in a deferred literal.
//
// @Ensures True
func RecoversLater() {
	defer func() {
		_ = recover() // want `vego: cannot verify RecoversLater: recover is not supported`
	}()
}

// WrapsUnknownLater wraps, in a deferred literal, the error a return set,
// which came from a parameter.
//
// @Ensures True
func WrapsUnknownLater(e error) (err error) {
	defer func() {
		if err != nil {
			err = fmt.Errorf("later: %w", err) // want `vego: cannot verify WrapsUnknownLater: formatting err would run the methods of an error whose origin is not known`
		}
	}()
	return e
}

// closeAll returns nil, and then a deferred literal replaces that with the
// error it was given. Its errors are therefore not all made here.
//
// @Ensures err = e
func closeAll(e error) (err error) {
	defer func() {
		if err == nil {
			err = e
		}
	}()
	return nil
}

// FormatsClosed formats the error of closeAll, which may be the parameter.
//
// @Ensures e = nil <-> err = nil
func FormatsClosed(e error) (err error) {
	if cerr := closeAll(e); cerr != nil {
		return fmt.Errorf("close: %w", cerr) // want `vego: cannot verify FormatsClosed: formatting cerr would run the methods of an error whose origin is not known`
	}
	return nil
}

// closeAllBound does the same with a deferred bound literal.
//
// @Ensures err = e
func closeAllBound(e error) (err error) {
	keep := func() {
		if err == nil {
			err = e
		}
	}
	defer keep()
	return nil
}

// AsksClosed asks errors.Is of the error of closeAllBound.
//
// @Ensures True
func AsksClosed(e error) (result bool) {
	return errors.Is(closeAllBound(e), ErrClosed) // want `vego: cannot verify AsksClosed: errors.Is would run the Is and Unwrap methods of closeAllBound\(e\), an error whose origin is not known`
}

// closeKnown replaces nil, in a deferred literal, only with errors made
// here, so its errors are of known origin.
//
// @Ensures fail <-> err != nil
func closeKnown(fail bool) (err error) {
	defer func() {
		if err == nil && fail {
			err = ErrClosed
		}
	}()
	return nil
}

// FormatsKnown formats the error of closeKnown.
//
// @Ensures fail <-> err != nil
func FormatsKnown(fail bool) (err error) {
	if cerr := closeKnown(fail); cerr != nil {
		return fmt.Errorf("close: %w", cerr)
	}
	return nil
}

// OverflowsInLiteral increments without a bound in a literal deferred
// inside another literal, which runs where that literal ends.
//
// @Ensures True
func OverflowsInLiteral(x int) (result int) {
	func() {
		defer func() { x++ }() // want `vego: addition may overflow int, in the function literal called at deferreddefects.go:145:2, in the function literal deferred at deferreddefects.go:146:9 and run at the end of the function literal at deferreddefects.go:147:2`
	}()
	return x
}
