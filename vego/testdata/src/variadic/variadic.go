// Package variadic holds calls of variadic functions: with their arguments
// listed, which makes a new slice, with none, which passes nil, and with a
// slice written with ..., which passes the slice itself.
package variadic

import (
	"errors"
	"io"
)

// Max returns the largest of its arguments.
//
// @Ensures m >= first
// @Ensures Forall i in [0, |rest|) : m >= rest[i]
func Max(first int, rest ...int) (m int) {
	m = first
	// @Invariant 0 <= i <= |rest|
	// @Invariant m >= first
	// @Invariant Forall j in [0, i) : m >= rest[j]
	// @Variant |rest| - i
	for i := 0; i < len(rest); i++ {
		if rest[i] > m {
			m = rest[i]
		}
	}
	return m
}

// @Ensures m >= 3
func MaxListed() (m int) {
	return Max(1, 2, 3)
}

// @Ensures m >= x
func MaxAlone(x int) (m int) {
	return Max(x)
}

// @Requires |xs| > 0
// @Ensures m >= xs[0]
func MaxSpread(x int, xs []int) (m int) {
	return Max(x, xs...)
}

// @Ensures m > 3
func MaxWrong() (m int) {
	return Max(1, 2, 3) // want `vego:\ postcondition\ may\ not\ hold:\ m\ >\ 3`
}

// Count returns how many arguments it was given.
//
// @Ensures n = |xs|
func Count(xs ...int) (n int) {
	return len(xs)
}

// @Requires |xs| >= 2
// @Ensures a = 3 And b = 0 And c = 2
func Counts(xs []int) (a, b, c int) {
	a = Count(7, 8, 9)
	b = Count()
	c = Count(xs[:2:2]...)
	return a, b, c
}

// @Ensures n = 1
func CountWrong() (n int) {
	return Count() // want `vego:\ postcondition\ may\ not\ hold:\ n\ =\ 1`
}

// Zero sets the first element of what it is given.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0] = 0
func Zero(xs ...int) {
	xs[0] = 0
}

// The listed arguments go into a new slice, which the callee may write
// without the caller listing anything.
//
// @Ensures True
func ZeroListed(a, b int) {
	Zero(a, b)
}

// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0] = 0
func ZeroSpread(xs []int) {
	Zero(xs...)
}

// A spread is the caller's slice: writing it needs the caller's leave.
//
// @Requires |xs| > 0
func ZeroUnlisted(xs []int) {
	Zero(xs...) // want `vego:\ Zero\ may\ modify\ xs,\ which\ ZeroUnlisted\ may\ not\ modify;\ list\ it\ in\ a`
}

// Zero may write all of a's capacity, which b lies in.
//
// @Requires |xs| = 3 And xs[1] = 5
// @Modifies xs
// @Ensures r = 5
func ZeroShared(xs []int) (r int) {
	a := xs[0:2]
	b := xs[1:3]
	Zero(a...)
	return b[0] // want `vego:\ postcondition\ may\ not\ hold:\ r\ =\ 5`
}

// With its capacity cut, a no longer reaches b.
//
// @Requires |xs| = 3 And xs[1] = 5
// @Modifies xs
// @Ensures r = 5
func ZeroCut(xs []int) (r int) {
	a := xs[0:1:1]
	b := xs[1:3]
	Zero(a...)
	return b[0]
}

// Pair assumes that its two slices share no memory.
//
// @Requires |a| > 0
// @Modifies a
// @Ensures a'[0] = |rest|
func Pair(a []int, rest ...int) {
	a[0] = len(rest)
}

// A new slice shares nothing with a.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0] = 2
func PairListed(xs []int) {
	Pair(xs, 1, 2)
}

// @Requires |xs| > 0
// @Modifies xs
func PairSame(xs []int) {
	Pair(xs, xs...) // want `vego:\ the\ slices\ passed\ to\ Pair\ as\ a\ and\ rest\ may\ overlap`
}

type P struct{ x int }

// SetFirst writes the struct that its first argument points to.
//
// @Requires |ps| > 0 And ps[0] != nil
// @Modifies ps[0]
// @Ensures ps[0].x' = 1
func SetFirst(ps ...*P) {
	ps[0].x = 1
}

// The new slice holds p, so what SetFirst writes is the caller's.
//
// @Requires p != nil
// @Modifies p
// @Ensures p.x' = 1
func SetThrough(p *P) {
	SetFirst(p)
}

// @Requires p != nil
func SetUnlisted(p *P) {
	SetFirst(p) // want `vego:\ SetFirst\ may\ modify\ .*which\ SetUnlisted\ may\ not\ modify`
}

// @Requires p != nil
// @Modifies p
// @Ensures p.x' = 0
func SetStale(p *P) {
	p.x = 0
	SetFirst(p)
} // want `vego:\ postcondition\ may\ not\ hold:\ p\.x'\ =\ 0`

// A loop forgets what the call in it writes through the new slice.
//
// @Requires p != nil And n > 0
// @Modifies p
// @Ensures p.x' = 0
func SetInLoop(p *P, n int) {
	p.x = 0
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		SetFirst(p)
	}
} // want `vego:\ postcondition\ may\ not\ hold:\ p\.x'\ =\ 0`

// @Requires p != nil And n > 0
// @Modifies p
// @Ensures p.x' = 1
func SetInLoopKnown(p *P, n int) {
	// @Invariant 0 <= i <= n
	// @Invariant i > 0 -> p.x = 1
	// @Variant n - i
	for i := 0; i < n; i++ {
		SetFirst(p)
	}
}

// CloseFirst closes the first value it is given.
//
// @Requires |cs| > 0 And cs[0] != nil And ~closed(cs[0])
// @Modifies cs[0]
// @Ensures closed(cs'[0])
func CloseFirst(cs ...io.Closer) {
	_ = cs[0].Close()
} // want `postcondition may not hold: closed\(cs'\[0\]\)`

// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures closed(c')
func CloseThrough(c io.Closer) {
	CloseFirst(c)
}

// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures ~closed(c')
func CloseStale(c io.Closer) {
	CloseFirst(c)
} // want `vego:\ postcondition\ may\ not\ hold:\ ~closed\(c'\)`

// Positive requires every argument to be positive.
//
// @Requires Forall i in [0, |xs|) : xs[i] > 0
// @Ensures True
func Positive(xs ...int) {
}

// The new slice of a deferred call is made at the defer statement.
//
// @Ensures True
func DeferredPack() {
	a := 1
	defer Positive(a, 2)
	a = -1
	_ = a
}

// @Ensures True
func DeferredPackWrong() {
	a := -1
	defer Positive(a, 2) // want `vego:\ precondition\ of\ Positive\ may\ not\ hold`
	a = 1
	_ = a
}

type Q struct{ n int }

// @Requires q != nil And q.n < 100
// @Modifies q
// @Ensures q.n' = q.n + 1 And r = q.n'
func bump(q *Q) (r int) {
	q.n++
	return q.n
}

// Go may read q.n before or after bump runs.
//
// @Requires q != nil And q.n < 100
// @Modifies q
// @Ensures True
func PackOrder(q *Q) {
	_ = Count(q.n, bump(q)) // want `vego:\ .*q\.n\ may\ be\ read\ before\ or\ after\ the\ call\ to\ bump`
}

// @Requires q != nil And q.n < 100
// @Modifies q
// @Ensures True
func PackOrdered(q *Q) {
	n := q.n
	_ = Count(n, bump(q))
}

// A variadic literal called where it is written.
//
// @Ensures n = 2
func LiteralInPlace() (n int) {
	return func(xs ...int) (k int) { return len(xs) }(4, 5)
}

// Hold takes values of any type and does nothing with them.
//
// @Ensures True
func Hold(vs ...any) {
}

// Each argument is converted to any.
//
// @Ensures True
func HoldMixed(s string) {
	Hold(1, s, nil)
}

// report is trusted, and keeps nothing it is given.
func report(errs ...error) {
}

// @Ensures True
func ReportMade() {
	report(errors.New("a"), io.EOF)
}

// @Ensures True
func ReportUnknown(err error) {
	report(err) // want `vego:\ cannot\ verify\ ReportUnknown:\ err\ is\ passed\ to\ report,\ which\ is\ trusted,\ and\ is\ an\ error\ whose\ origin\ is\ not\ known`
}

// @Ensures True
func ReportSpread(errs []error) {
	report(errs...) // want `vego:\ cannot\ verify\ ReportSpread:\ errs\ is\ passed\ to\ report,\ which\ is\ trusted,\ and\ is\ a\ value\ of\ type\ \[\]error`
}

// join is trusted.
func join(parts ...string) (s string) {
	s = ""
	for _, p := range parts {
		s += p
	}
	return s
}

// @Ensures |s| >= 2
func Joined(a string) (s string) {
	return join(a, "b") // want `vego:\ postcondition\ may\ not\ hold:\ \|s\|\ >=\ 2`
}
