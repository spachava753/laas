// Package runinv holds invariants of the runs of what a call hands over,
// written above the statement that makes the call (O1 of the review of the
// end of F40), and their defects.
package runinv

import (
	"sort"
	"strings"
)

// each calls f with every element of xs.
//
// @Calls f(x) When 0 <= x < 100
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func each(xs []int, f func(int)) {
	for _, x := range xs {
		f(x)
	}
}

// Count counts the runs, guarded by the length.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures 0 <= n <= |xs|
func Count(xs []int) (n int) {
	// @Invariant 0 <= n <= |xs|
	each(xs, func(x int) {
		if n < len(xs) {
			n++
		}
	})
	return n
}

// Sum adds bounded elements, guarded by a bound.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures 0 <= s <= 1000000
func Sum(xs []int) (s int) {
	// @Invariant 0 <= s <= 1000000
	each(xs, func(x int) {
		if s <= 1000000-x {
			s += x
		}
	})
	return s
}

// Collect appends, with the length bounded.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures |out| <= 1000
func Collect(xs []int) (out []int) {
	// @Invariant |out| <= 1000
	each(xs, func(x int) {
		if len(out) < 1000 {
			out = append(out, x)
		}
	})
	return out
}

// Fill fills a map with values the invariant states.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures seen != nil And Forall k in seen : seen[k]
func Fill(xs []int) (seen map[int]bool) {
	seen = make(map[int]bool)
	// @Invariant seen != nil And Forall k in seen : seen[k]
	each(xs, func(x int) {
		seen[x] = true
	})
	return seen
}

// NotAtCall states what does not hold at the call.
//
// @Ensures True
func NotAtCall(xs []int) {
	n := 5
	// @Invariant n = 0 // want `invariant may not hold where each is called: n = 0`
	each(nil, func(x int) {})
	_ = n
}

// Broken breaks it in a run.
//
// @Ensures True
func Broken() {
	n := 0
	// @Invariant n = 0 // want `invariant may not be kept by the function literal run by each: n = 0`
	each(nil, func(x int) { n = 1 })
	_ = n
}

// EarlyReturn breaks it on one way out.
//
// @Ensures True
func EarlyReturn() {
	n := 0
	// @Invariant 0 <= n <= 1 // want `invariant may not be kept by the function literal run by each: 0 <= n <= 1`
	each(nil, func(x int) {
		if x > 50 {
			n = 2
			return
		}
		n = 1
	})
	_ = n
}

// Searched relies on an applied callback with an invariant false at the call (F28).
//
// @Ensures True
func Searched(s []int) (i int) {
	k := 1
	// @Invariant k = 0 // want `invariant may not hold where sort.Search is called: k = 0`
	return sort.Search(len(s), func(i int) bool { return s[i] >= k })
}

// TwoCalls has two handing calls in one statement.
//
// @Ensures True
func TwoCalls(s string) (n int) {
	c := 0
	// @Invariant 0 <= c // want `an Invariant annotation above a statement describes the runs of what one call hands over, and this statement makes several calls that hand functions over; make each call in a statement of its own`
	n = strings.IndexFunc(s, func(r rune) bool { return true }) + strings.IndexFunc(s, func(r rune) bool { return false })
	return n + c
}

// NoCall has no handing call.
//
// @Ensures True
func NoCall() {
	n := 0
	// @Invariant n = 0 // want `an Invariant annotation must be directly above a for loop, or above a statement that makes one call handing a function literal to a parameter with a contract under calls or Calls, whose runs it describes`
	n++
}

func isA(r rune) bool { return r == 'a' }

// ValueOnly hands a function, not a literal.
//
// @Ensures True
func ValueOnly(s string) (n int) {
	// @Invariant 0 <= n // want `an Invariant annotation above a call describes the runs of the function literals it hands over, and this call hands none: a function or a method value writes the caller's variables only by its contract`
	n = strings.IndexFunc(s, isA) // want `cannot verify ValueOnly: it hands isA to IndexFunc, and isA has no contract`
	return n
}

// Nested: the inner call's invariant stands inside the outer literal.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures 0 <= n <= 10
func Nested(xs []int) (n int) {
	// @Invariant 0 <= n <= 10
	each(xs, func(x int) {
		// @Invariant 0 <= n <= 10
		each(xs, func(y int) {
			if n < 10 {
				n++
			}
		})
	})
	return n
}

// InIf: the call in an if condition.
//
// @Ensures True
func InIf(s string) {
	c := 0
	// @Invariant 0 <= c <= 1
	if strings.IndexFunc(s, func(r rune) bool { c = 1; return r == 'a' }) >= 0 {
		c = 3
	}
	_ = c
}

// InReturn returns what the call returns; c is read after it.
//
// @Ensures 0 <= c <= 1
func InReturn(s string) (n, c int) {
	// @Invariant 0 <= c <= 1
	return strings.IndexFunc(s, func(r rune) bool { c = 1; return r == 'a' }), 0
}

// InSwitch makes the call in the tag of a switch.
//
// @Ensures True
func InSwitch(s string) {
	c := 0
	// @Invariant 0 <= c <= 1
	switch strings.IndexFunc(s, func(r rune) bool { c = 1; return r == 'a' }) {
	case 0:
		c = 2
	}
	_ = c
}

// InLoop hands a literal inside a loop: the loop's head forgets what the
// call writes, so its own invariant says what the runs keep.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures 0 <= n <= 10
func InLoop(xs []int) (n int) {
	// @Invariant 0 <= n <= 10
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		// @Invariant 0 <= n <= 10
		each(xs, func(x int) {
			if n < 10 {
				n++
			}
		})
	}
	return n
}

// InLoopForgotten has no loop invariant: what the runs keep is not known
// at the head of the loop.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func InLoopForgotten(xs []int) (n int) {
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		// @Invariant 0 <= n <= 10 // want `invariant may not hold where each is called: 0 <= n <= 10`
		each(xs, func(x int) {
			if n < 10 {
				n++
			}
		})
	}
	return n
}

// InCondition makes the call in the condition of a for loop, whose
// invariant above it is the loop's: the runs get none.
//
// @Ensures True
func InCondition(s string) {
	c := 0
	// @Invariant 0 <= c
	for strings.IndexFunc(s, func(r rune) bool { c = 1; return r == 'a' }) > 100 { // want `loop needs a // @Variant annotation to prove that it terminates`
		c = 0
	}
	_ = c
}

// Deferred puts the call off, when nothing of the statement is known.
//
// @Ensures True
func Deferred(xs []int) {
	n := 0
	// @Invariant n = 0 // want `an Invariant annotation must be directly above a for loop, or above a statement that makes one call handing a function literal`
	defer each(nil, func(x int) {}) // want `cannot verify Deferred: deferring a call of each, which calls a function it is given, is not supported yet`
	_ = n
}
