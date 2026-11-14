// Package guide holds the programs of docs/verification.md, so that what the
// guide says verifies does, and what it says is reported is.
package guide

import (
	"errors"
	"fmt"
	"strconv"
)

// Max returns the larger of two numbers.
func Max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

//@ Ensures result >= a And result >= b
//@ Ensures result = a Or result = b

// MaxWrong has a contract its body does not meet.
func MaxWrong(a, b int) int {
	if a > b {
		return b // want `vego: postcondition may not hold: result >= a`
	}
	return b
}

//@ Ensures result >= a And result >= b

// AbsWrong forgets the one number that has no positive counterpart.
func AbsWrong(x int) int {
	if x < 0 {
		return -x // want `vego: negation may overflow int`
	}
	return x
}

//@ Ensures result >= 0

// Abs rules that number out.
//
// @ Requires x > MinInt
func Abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

//@ Ensures result >= 0 And (result = x Or result = -x)

// MidWrong adds two numbers that may not fit together.
//
// @ Requires 0 <= lo <= hi
func MidWrong(lo, hi int) int {
	return (lo + hi) / 2 // want `vego: addition may overflow int`
}

//@ Ensures lo <= result <= hi

// Mid computes the same without leaving the type.
//
// @ Requires 0 <= lo <= hi
func Mid(lo, hi int) int {
	return lo + (hi-lo)/2
}

//@ Ensures lo <= result <= hi

// FirstWrong reads an element that may not be there.
func FirstWrong(A []int) int {
	return A[0] // want `vego: index may be out of range`
}

//@ Ensures result = A[0]

// First asks its callers for a slice that has one.
//
// @ Requires |A| > 0
func First(A []int) int {
	return A[0]
}

//@ Ensures result = A[0]

// Divide computes quotient and remainder by repeated subtraction.
//
// @ Requires n >= 0 And d > 0
func Divide(n, d int) (q, r int) {
	q, r = 0, n
	//@ Invariant n = d*q + r And 0 <= r
	//@ Variant r
	for d <= r {
		q, r = q+1, r-d
	}
	return q, r
}

//@ Ensures n = d*q + r And 0 <= r < d

// Sum adds up numbers that are known to be small.
//
// @ Requires |A| <= 1000
// @ Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
func Sum(A []int) int {
	total := 0
	//@ Invariant 0 <= total <= 1000 * i
	for i := range A {
		total += A[i]
	}
	return total
}

//@ Ensures 0 <= result <= 1000 * |A|

// Index returns where x first occurs, or -1.
func Index(A []int, x int) int {
	//@ Invariant Forall k in [0, i) : A[k] != x
	for i := range A {
		if A[i] == x {
			return i
		}
	}
	return -1
}

//@ Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
//@ Ensures result = -1 -> Forall k in [0, |A|) : A[k] != x

// Steps counts down to zero by calling itself.
//
// @ Requires n >= 0
// @ Measure n
func Steps(n int) int {
	if n == 0 {
		return 0
	}
	return 1 + Steps(n-1)
}

//@ Ensures result = n

// Cell numbers the cells of a grid row by row.
//
// @ Requires 0 <= i < h And 0 <= j < w And h <= 1000 And w <= 1000
func Cell(i, j, w, h int) int {
	return i*w + j
}

//@ Ensures 0 <= result < h*w

// Clamp brings x into a range.
//
// @ Requires lo <= hi
func Clamp(x, lo, hi int) int {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}

//@ Ensures lo <= result <= hi

// Percent relies on what Clamp promises and on nothing else about it.
func Percent(x int) int {
	return Clamp(x, 0, 100)
}

//@ Ensures 0 <= result <= 100

func helper(x int) int { return x }

// CallsHelper calls a function that has no contract.
func CallsHelper(x int) int {
	return helper(x) // want `vego: cannot verify CallsHelper: it calls helper, which has no contract; annotate helper with //@ so that it is verified, or add a trusted contract for guide.helper to vego-trusted.yaml`
}

//@ Ensures result = x

//@ Predicate sorted(A) ::= Forall i, j in [0, |A|) : i <= j -> A[i] <= A[j]

// Smallest returns the least element of a sorted slice.
//
// @ Requires sorted(A) And |A| > 0
func Smallest(A []int) int {
	return A[0]
}

//@ Ensures Forall k in [0, |A|) : result <= A[k]

// Fill sets every element.
//
// @ Modifies A
func Fill(A []int, v int) {
	//@ Invariant Forall k in [0, i) : A[k] = v
	for i := range A {
		A[i] = v
	}
}

//@ Ensures Forall k in [0, |A|) : A'[k] = v

// FillUnlisted writes a slice without saying so.
func FillUnlisted(A []int, v int) {
	for i := range A {
		A[i] = v // want `vego: A\[i\] is assigned, which FillUnlisted may not modify; list it in a //@ Modifies clause`
	}
}

//@ Ensures True

// Push appends, which writes into the capacity of A or moves to a new array.
//
// @ Requires |A| < 1000
// @ Modifies A
func Push(A []int, x int) []int {
	return append(A, x)
}

//@ Ensures |result| = |A| + 1 And result[|A|] = x

// Counter counts up to a limit.
type Counter struct {
	n     int
	limit int
}

// NewCounter returns a counter nobody else has.
func NewCounter(limit int) *Counter {
	return &Counter{limit: limit}
}

//@ Ensures fresh(result) And result.n = 0 And result.limit = limit

// Inc advances the counter and leaves its limit alone.
//
// @ Requires c != nil And c.n < c.limit
// @ Modifies c.n
func (c *Counter) Inc() {
	c.n++
}

//@ Ensures c.n' = c.n + 1

// Twice works on a counter through its methods' contracts.
//
// @ Requires c != nil And c.n = 0 And c.limit = 10
// @ Modifies c.n
func Twice(c *Counter) {
	c.Inc()
	c.Inc()
}

//@ Ensures c.n' = 2 And c.limit' = 10

// SameOrNot writes through two pointers that may be one.
//
// @ Requires a != nil And b != nil
// @ Modifies a.n, b.n
func SameOrNot(a, b *Counter) int {
	a.n = 1
	b.n = 2
	return a.n // want `vego: postcondition may not hold: result = 1`
}

//@ Ensures result = 1

// Different says that they are not.
//
// @ Requires a != nil And b != nil And a != b
// @ Modifies a.n, b.n
func Different(a, b *Counter) int {
	a.n = 1
	b.n = 2
	return a.n
}

//@ Ensures result = 1

// Stack keeps a count that never exceeds what it holds.
//
// @ Invariant 0 <= n <= |items|
type Stack struct {
	items []int
	n     int
}

// Top may index with n-1 because the invariant bounds n.
//
// @ Requires s != nil And s.n > 0
func (s *Stack) Top() int {
	return s.items[s.n-1]
}

//@ Ensures result = s.items[s.n-1]

// Get reads a key that may be absent.
func Get(m map[string]int, k string) (v int, err error) {
	v, ok := m[k]
	if !ok {
		return 0, ErrMissing
	}
	return v, nil
}

//@ Ensures err = nil <-> has(m, k)
//@ Ensures err = nil -> v = m[k]

// Bump counts one more for a key.
//
// @ Requires m != nil And m[k] < 1000
// @ Modifies m
func Bump(m map[string]int, k string) {
	m[k] = m[k] + 1
}

//@ Ensures has(m', k) And m'[k] = m[k] + 1

// ErrMissing and ErrEmpty are errors that are known not to be nil.
var (
	ErrMissing = errors.New("missing")
	ErrEmpty   = errors.New("empty")
	ErrRange   = errors.New("out of range")
)

// Head says when it succeeds and what it returns then.
func Head(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

//@ Ensures err = nil <-> |A| > 0
//@ Ensures err = nil -> first = A[0]

// HeadWeak only says what success looks like.
func HeadWeak(A []int) (first int, err error) { // want `vego: the contract of HeadWeak may also be met by a function that always returns an error.*`
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

//@ Ensures err = nil -> first = A[0]

// At makes an error that says what went wrong.
func At(A []int, i int) (x int, err error) {
	if i < 0 || i >= len(A) {
		return 0, fmt.Errorf("index %d out of range", i)
	}
	return A[i], nil
}

//@ Ensures err = nil <-> 0 <= i < |A|
//@ Ensures err = nil -> x = A[i]

// ParsePort relies on the contract that ships for strconv.Atoi.
func ParsePort(s string) (port int, err error) {
	n, err := strconv.Atoi(s)
	if err != nil {
		return 0, err
	}
	if n < 1 || n > 65535 {
		return 0, ErrRange
	}
	return n, nil
}

//@ Ensures err = nil -> 1 <= port <= 65535

// Lock is held or not.
type Lock struct{ held bool }

// Acquire takes the lock.
//
// @ Requires l != nil And ~l.held
// @ Modifies l
func (l *Lock) Acquire() {
	l.held = true
}

//@ Ensures l.held'

// Release gives the lock back.
//
// @ Requires l != nil And l.held
// @ Modifies l
func (l *Lock) Release() {
	l.held = false
}

//@ Ensures ~l.held'

// Guarded gives the lock back on every way out.
//
// @ Requires l != nil And ~l.held And c != nil And c.n < c.limit
// @ Modifies l, c.n
func Guarded(l *Lock, c *Counter, skip bool) {
	l.Acquire()
	defer l.Release()
	if skip {
		return
	}
	c.Inc()
}

//@ Ensures ~l.held'

// Pack puts two bytes into sixteen bits.
func Pack(hi, lo byte) uint16 {
	return uint16(hi)<<8 | uint16(lo)
}

//@ Ensures result = 256 * hi + lo

// Join concatenates two strings of bounded length.
//
// @ Requires |a| <= 1000 And |b| <= 1000
func Join(a, b string) string {
	return a + b
}

//@ Ensures |result| = |a| + |b|

// IsAdmin compares a string with a literal.
func IsAdmin(role string) bool {
	return role == "admin"
}

//@ Ensures result <-> role = "admin"
