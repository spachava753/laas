// Package closures holds function literals used where they are written:
// called on the spot, or bound to a variable that is only called. Each is
// verified at its calls as part of the function around it.
package closures

import (
	"errors"
	"fmt"
)

// Called reads the variables of the function around it when it runs.
//
// @Requires 0 <= x < 100
// @Ensures result = x + 1
func Called(x int) (result int) {
	return func() int { return x + 1 }()
}

// CalledLater sees the value a variable has when the literal runs, not
// when it is written.
//
// @Requires 0 <= x < 100
// @Ensures result = 2*x + 1
func CalledLater(x int) (result int) {
	y := x
	next := func() int { return y + 1 }
	y = 2 * x
	return next()
}

// Less is a comparison bound to a variable and called in conditions.
//
// @Requires |A| = 3
// @Ensures result <-> A[0] < A[1] And A[1] < A[2]
func Less(A []int) (result bool) {
	less := func(i, j int) bool { return A[i] < A[j] }
	if less(0, 1) && less(1, 2) {
		return true
	}
	return false
}

// Branches calls a literal that returns in two places, inside an
// expression.
//
// @Requires MinInt < a And MinInt < b And -1000 <= a <= 1000 And -1000 <= b <= 1000
// @Ensures result >= 0 And (result = a + b Or result = -a + b Or result = a - b Or result = -a - b)
func Branches(a, b int) (result int) {
	abs := func(n int) int {
		if n < 0 {
			return -n
		}
		return n
	}
	return abs(a) + abs(b)
}

// Writes changes memory through a literal, as its Modifies clause allows.
//
// @Requires |A| >= 2
// @Modifies A
// @Ensures A'[0] = 7 And A'[1] = 8
func Writes(A []int) {
	set := func(i, x int) { A[i] = x }
	set(0, 7)
	set(1, 8)
}

// Guarded calls a literal on the right of &&: its index is in range only
// where the left side holds.
//
// @Ensures result -> 0 <= i < |A| And A[i] > 0
func Guarded(A []int, i int) (result bool) {
	positive := func(k int) bool { return A[k] > 0 }
	return 0 <= i && i < len(A) && positive(i)
}

// Loops runs a loop inside a literal.
//
// @Requires |A| <= 1000 And Forall k in [0, |A|) : 0 <= A[k] <= 1000
// @Ensures 0 <= result <= 1000 * |A|
func Loops(A []int) (result int) {
	sum := func() int {
		total := 0
		// @Invariant 0 <= total <= 1000 * i
		for i := range A {
			total += A[i]
		}
		return total
	}
	return sum()
}

// Nested calls a literal from inside another.
//
// @Requires 0 <= x < 100
// @Ensures result = x + 2
func Nested(x int) (result int) {
	inc := func(n int) int { return n + 1 }
	twice := func(n int) int { return inc(inc(n)) }
	return twice(x)
}

// EndsEarly returns from the literal only, and the function goes on.
//
// @Requires |A| >= 1
// @Modifies A
// @Ensures A'[0] = 1
func EndsEarly(A []int, skip bool) {
	func() {
		if skip {
			return
		}
		A[0] = 2
	}()
	A[0] = 1
}

// Asserts checks an assertion inside the body at each call.
//
// @Requires 0 <= x < 100
// @Ensures result = x
func Asserts(x int) (result int) {
	id := func(n int) int {
		// @Assert n < 100
		return n
	}
	return id(x)
}

// Deferred puts off a named call inside a literal, which runs when the
// literal returns.
//
// @Requires g != nil
// @Modifies g
// @Ensures g.v' = 2
func Deferred(g *Gauge) {
	func() {
		defer g.Set(1)
	}()
	g.Set(2)
}

// DefersInEachIteration puts off a call in a literal that each iteration
// calls; the call runs at the end of the literal, once per iteration.
//
// @Requires g != nil And 0 <= n <= 3
// @Modifies g
func DefersInEachIteration(g *Gauge, n int) {
	// @Invariant 0 <= i <= n
	for i := range n {
		func() {
			defer g.Set(i)
		}()
	}
}

// KeepsAcrossJoin calls, in a loop, a literal that ends in two ways and
// writes one slice; what the loop keeps of another slice is still known
// after the call.
//
// @Requires |A| = |B| And |B| >= 1
// @Modifies A
// @Ensures B'[0] = B[0]
func KeepsAcrossJoin(A, B []int, flip bool) {
	put := func(i int) {
		if flip {
			A[i] = 1
			return
		}
		A[i] = 2
	}
	// @Invariant 0 <= i <= |A|
	for i := range A {
		put(i)
		// @Assert B[0] = old(B[0])
	}
}

// WrapsKnown formats an error that the literal is given, which is of
// known origin at its only call.
//
// @Ensures result
func WrapsKnown() (result bool) {
	wrap := func(x error) error { return fmt.Errorf("w: %w", x) }
	return wrap(ErrBase) != nil
}

var ErrBase = errors.New("base")

// Gauge holds a number.
type Gauge struct{ v int }

// @Requires g != nil
// @Modifies g.v
// @Ensures g.v' = v
func (g *Gauge) Set(v int) {
	g.v = v
}

// GuardKeeps knows that a literal on the right of && that did not run
// changed nothing.
//
// @Requires |A| >= 1
// @Modifies A
// @Ensures c -> A'[0] = 5
// @Ensures ~c -> A'[0] = A[0]
func GuardKeeps(A []int, c bool) {
	if c && func() bool { A[0] = 5; return true }() {
		return
	}
}

// Chain joins one region 32 times: a literal with two ends that writes
// memory, called again and again. What a join makes must not grow with
// the joins before it.
//
// @Requires g != nil
// @Modifies g.v
// @Ensures result = 0 Or result = 1
func Chain(g *Gauge, c bool) (result int) {
	g.v = 0
	bump := func() {
		if c {
			g.v = 1
		}
	}
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	bump()
	return g.v
}

// ChainValue joins a value 32 times through the result of a literal with
// two ends.
//
// @Requires 0 <= x <= 1000
// @Ensures x <= result <= x + 32
func ChainValue(x int) (result int) {
	step := func(n int) int {
		if n < 2000 {
			return n + 1
		}
		return n
	}
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	x = step(x)
	return x
}
