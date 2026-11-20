// Package ensuresentry has Ensures clauses that speak only of the state
// on entry: those that read memory the function may modify are refused,
// and those that speak of the return, or read nothing it may change, are
// kept.
package ensuresentry

import (
	"io"
	"sync"
)

// Point is a pair of numbers.
type Point struct {
	x, y int
}

// Stack holds items.
type Stack struct {
	items []int
	mu    sync.Mutex
}

// @Predicate sorted(A) ::= Forall i, j in [0, |A|) : i <= j -> A[i] <= A[j]

// @Predicate zeros(A, n) ::= n <= 0 Or (zeros(A, n-1) And A[n-1] = 0)

// @Requires p != nil And p.x = 7
// @Modifies p.x
// @Ensures p.x = 7 // want `the Ensures clause "p.x = 7" names no result and nothing on return, so it speaks of the state when SetX is called, and it reads memory that SetX may modify; write a prime for the value on return, as in p.x', or move the clause to a Requires`
func SetX(p *Point) {
	p.x = 7
}

// @Requires p != nil And p.x = 7
// @Modifies p.x
// @Ensures r >= 0 And p.x = 7 // want `the Ensures clause "p.x = 7", in "r >= 0 And p.x = 7", names no result`
func Conjunct(p *Point) (r int) {
	p.x = 7
	return 0
}

// @Requires sorted(A)
// @Modifies A
// @Ensures sorted(A) // want `the Ensures clause "sorted\(A\)" names no result.*as in A'`
func Sorted(A []int) {
	if len(A) > 0 {
		A[0] = A[0]
	}
}

// @Requires zeros(A, |A|)
// @Modifies A
// @Ensures zeros(A, |A|) // want `the Ensures clause "zeros\(A, \|A\|\)" names no result`
func Zeros(A []int) {
	if len(A) > 0 {
		A[0] = 0
	}
}

// @Requires Forall i in [0, |A|) : A[i] = 0
// @Modifies A
// @Ensures Forall i in [0, |A|) : A[i] = 0 // want `the Ensures clause "Forall i in \[0, \|A\|\) : A\[i\] = 0" names no result.*as in A'\[i\]`
func Quantified(A []int) {
	if len(A) > 0 {
		A[0] = 0
	}
}

// @Requires has(m, 1)
// @Modifies m
// @Ensures has(m, 1) // want `the Ensures clause "has\(m, 1\)" names no result`
func Has(m map[int]int) {
	m[1] = 2
}

// @Requires s != nil And |s.items| <= 10
// @Modifies s
// @Ensures |s.items| <= 10 // want `the Ensures clause "\|s.items\| <= 10" names no result.*as in s.items'`
func Length(s *Stack) {
	s.items = s.items[:0]
}

// @Requires s != nil And ~held(s.mu)
// @Modifies s.mu
// @Ensures ~held(s.mu) // want `the Ensures clause "~held\(s.mu\)" names no result.*as in s.mu'`
func Held(s *Stack) {
	s.mu.Lock()
	s.mu.Unlock()
}

// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures ~closed(c) // want `the Ensures clause "~closed\(c\)" names no result.*as in c'`
func Closed(c io.Closer) {
	c.Close()
}

// These are kept.

// @Requires p != nil
// @Modifies p.x
// @Ensures r = p.x And p.x' = 7
func Swap(p *Point) (r int) {
	r = p.x
	p.x = 7
	return r
}

// @Requires p != nil
// @Modifies p.x
// @Ensures ok -> p.x = 7
func Guarded(p *Point) (ok bool) {
	ok = p.x == 7
	p.x = 1
	return ok
}

// @Requires p != nil And p.x < 100
// @Modifies p.x
// @Ensures p.x' = p.x + 1
func Increment(p *Point) {
	p.x++
}

// @Requires s != nil And |s.items| < 1000
// @Modifies s, s.items
// @Ensures fresh(s.items) Or within(s.items', s.items)
func Push(s *Stack) {
	s.items = append(s.items, 1)
}

// @Requires |A| = 5
// @Modifies A
// @Ensures |A| = 5
func Header(A []int) {
	A[0] = 1
}

// @Requires p != nil And q != nil And q.y = 3
// @Modifies p.x
// @Ensures q.y = 3
func Other(p, q *Point) {
	p.x = 1
}

// @Requires n > 0
// @Ensures n > 0
func Value(n int) {
}

// Step has a contract on its type.
//
// @Requires p != nil And p.x = 1
// @Modifies p
// @Ensures p.x = 1 // want `the Ensures clause "p.x = 1" names no result and nothing on return, so it speaks of the state when Step is called`
type Step func(p *Point)

// Mover has a method with a contract.
type Mover interface {
	// @Requires p != nil And p.y = 2
	// @Modifies p
	// @Ensures p.y = 2 // want `the Ensures clause "p.y = 2" names no result and nothing on return, so it speaks of the state when Mover.Move is called`
	Move(p *Point)
}

func trusted(p *Point) {}

// @Requires p != nil And p.x = 3
// @Modifies p
// @Ensures True
func UsesTrusted(p *Point) {
	trusted(p) // want `the Ensures clause "p.x = 3" names no result and nothing on return, so it speaks of the state when trusted is called`
}
