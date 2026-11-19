package closures

import (
	"errors"
	"fmt"
)

func closeIt() (err error) { return nil }

var ErrClosed = errors.New("closed")

// SetsLater changes a named result in a literal deferred before the
// return, which runs after the return has set the result.
//
// @Ensures result = 2
func SetsLater() (result int) {
	defer func() { result = 2 }()
	return 1
}

// SeesResult reads the result the return set.
//
// @Requires 0 <= x < 1000
// @Ensures x > 0 -> result = x + 1
// @Ensures x = 0 -> result = 0
func SeesResult(x int) (result int) {
	defer func() {
		if result > 0 {
			result++
		}
	}()
	return x
}

// ClosesAfter keeps the first error: the error of closing only when
// nothing failed before.
//
// @Requires g != nil
// @Modifies g.v
// @Ensures g.v' = 1
func ClosesAfter(g *Gauge) (err error) {
	defer func() {
		if cerr := closeIt(); err == nil {
			err = cerr
		}
	}()
	g.Set(1)
	return nil
}

// TakesArgumentEarly gives the literal an argument at the defer statement,
// and reads a captured variable when it runs.
//
// @Requires g != nil And h != nil And g != h
// @Modifies g.v, h.v
// @Ensures g.v' = x And h.v' = 5
func TakesArgumentEarly(g, h *Gauge, x int) {
	defer func(n int) { g.Set(n) }(x)
	defer func() { h.Set(x) }()
	x = 5
}

// RunsLastFirst puts off two literals, which run in the opposite order.
//
// @Requires g != nil
// @Modifies g.v
// @Ensures g.v' = 1
func RunsLastFirst(g *Gauge) {
	defer func() { g.Set(1) }()
	defer func() { g.Set(2) }()
}

// DefersBound puts off a literal bound to a variable, and calls it too.
//
// @Requires g != nil
// @Modifies g.v
// @Ensures g.v' = 3
func DefersBound(g *Gauge) {
	reset := func() { g.Set(3) }
	defer reset()
	reset()
	g.Set(4)
}

// ReadsBlockLater puts off, in a block, a literal that reads a variable of
// the block; it runs at the return, after the block has ended.
//
// @Requires g != nil
// @Modifies g.v
// @Ensures g.v' = 2
func ReadsBlockLater(g *Gauge) {
	{
		n := 1
		defer func() { g.Set(n) }()
		n = 2
	}
}

// EndsInTwoWays puts off a literal whose body ends in two ways.
//
// @Requires g != nil
// @Modifies g.v
// @Ensures c -> g.v' = 1
// @Ensures ~c -> g.v' = 2
func EndsInTwoWays(g *Gauge, c bool) {
	defer func() {
		if c {
			g.Set(1)
			return
		}
		g.Set(2)
	}()
}

// DefersInLiteral puts off a literal inside a literal, where it runs when
// the outer literal returns.
//
// @Requires g != nil
// @Modifies g.v
// @Ensures g.v' = 2
func DefersInLiteral(g *Gauge) {
	func() {
		defer func() { g.Set(1) }()
	}()
	g.Set(2)
}

// DefersInEachCall puts off a literal in a literal that each iteration
// calls.
//
// @Requires g != nil And 0 <= n <= 3
// @Modifies g.v
func DefersInEachCall(g *Gauge, n int) {
	// @Invariant 0 <= i <= n
	for i := range n {
		func() {
			defer func() { g.Set(i) }()
		}()
	}
}

// WrapsKnownLater wraps, in a deferred literal, an error the function
// made.
//
// @Ensures fail -> err != nil
// @Ensures ~fail -> err = nil
func WrapsKnownLater(fail bool) (err error) {
	defer func() {
		if err != nil {
			err = fmt.Errorf("later: %w", err)
		}
	}()
	if fail {
		return ErrClosed
	}
	return nil
}
