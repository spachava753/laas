// Package guide holds the programs of docs/verification.md, so that what the
// guide says verifies does, and what it says is reported is.
package guide

import (
	"errors"
	"fmt"
	"io"
	"os"
	"sort"
	"strconv"
	"sync"
)

// Max returns the larger of two numbers.
//
// @Ensures result >= a And result >= b
// @Ensures result = a Or result = b
func Max(a, b int) (result int) {
	if a > b {
		return a
	}
	return b
}

// MaxWrong has a contract its body does not meet.
//
// @Ensures result >= a And result >= b
func MaxWrong(a, b int) (result int) {
	if a > b {
		return b // want `vego: postcondition may not hold: result >= a`
	}
	return b
}

// AbsWrong forgets the one number that has no positive counterpart.
//
// @Ensures result >= 0
func AbsWrong(x int) (result int) {
	if x < 0 {
		return -x // want `vego: negation may overflow int`
	}
	return x
}

// Abs rules that number out.
//
// @Requires x > MinInt
// @Ensures result >= 0 And (result = x Or result = -x)
func Abs(x int) (result int) {
	if x < 0 {
		return -x
	}
	return x
}

// MidWrong adds two numbers that may not fit together.
//
// @Requires 0 <= lo <= hi
// @Ensures lo <= result <= hi
func MidWrong(lo, hi int) (result int) {
	return (lo + hi) / 2 // want `vego: addition may overflow int`
}

// Mid computes the same without leaving the type.
//
// @Requires 0 <= lo <= hi
// @Ensures lo <= result <= hi
func Mid(lo, hi int) (result int) {
	return lo + (hi-lo)/2
}

// FirstWrong reads an element that may not be there.
//
// @Ensures result = A[0]
func FirstWrong(A []int) (result int) {
	return A[0] // want `vego: index may be out of range`
}

// First asks its callers for a slice that has one.
//
// @Requires |A| > 0
// @Ensures result = A[0]
func First(A []int) (result int) {
	return A[0]
}

// Divide computes quotient and remainder by repeated subtraction.
//
// @Requires n >= 0 And d > 0
// @Ensures n = d*q + r And 0 <= r < d
func Divide(n, d int) (q, r int) {
	q, r = 0, n
	// @Invariant n = d*q + r And 0 <= r
	// @Variant r
	for d <= r {
		q, r = q+1, r-d
	}
	return q, r
}

// Sum adds up numbers that are known to be small.
//
// @Requires |A| <= 1000
// @Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
// @Ensures 0 <= result <= 1000 * |A|
func Sum(A []int) (result int) {
	total := 0
	// @Invariant 0 <= total <= 1000 * i
	for i := range A {
		total += A[i]
	}
	return total
}

// Index returns where x first occurs, or -1.
//
// @Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
// @Ensures result = -1 -> Forall k in [0, |A|) : A[k] != x
func Index(A []int, x int) (result int) {
	// @Invariant Forall k in [0, i) : A[k] != x
	for i := range A {
		if A[i] == x {
			return i
		}
	}
	return -1
}

// Steps counts down to zero by calling itself.
//
// @Requires n >= 0
// @Variant n
// @Ensures result = n
func Steps(n int) (result int) {
	if n == 0 {
		return 0
	}
	return 1 + Steps(n-1)
}

// Cell numbers the cells of a grid row by row.
//
// @Requires 0 <= i < h And 0 <= j < w And h <= 1000 And w <= 1000
// @Ensures 0 <= result < h*w
func Cell(i, j, w, h int) (result int) {
	return i*w + j
}

// Clamp brings x into a range.
//
// @Requires lo <= hi
// @Ensures lo <= result <= hi
func Clamp(x, lo, hi int) (result int) {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}

// Percent relies on what Clamp promises and on nothing else about it.
//
// @Ensures 0 <= result <= 100
func Percent(x int) (result int) {
	return Clamp(x, 0, 100)
}

func helper(x int) int { return x }

// CallsHelper calls a function that has no contract.
//
// @Ensures result = x
func CallsHelper(x int) (result int) {
	return helper(x) // want `vego: cannot verify CallsHelper: it calls helper, which has no contract; annotate helper with // @ annotations so that it is verified, or add a trusted contract for guide.helper to vego-trusted.yaml`
}

// @Predicate sorted(A) ::= Forall i, j in [0, |A|) : i <= j -> A[i] <= A[j]

// Smallest returns the least element of a sorted slice.
//
// @Requires sorted(A) And |A| > 0
// @Ensures Forall k in [0, |A|) : result <= A[k]
func Smallest(A []int) (result int) {
	return A[0]
}

// Fill sets every element.
//
// @Modifies A
// @Ensures Forall k in [0, |A|) : A'[k] = v
func Fill(A []int, v int) {
	// @Invariant Forall k in [0, i) : A[k] = v
	for i := range A {
		A[i] = v
	}
}

// FillUnlisted writes a slice without saying so.
//
// @Ensures True
func FillUnlisted(A []int, v int) {
	for i := range A {
		A[i] = v // want `vego: A\[i\] is assigned, which FillUnlisted may not modify; list it in a // @Modifies clause, as A`
	}
}

// Push appends, which writes into the capacity of A or moves to a new array.
//
// @Requires |A| < 1000
// @Modifies A
// @Ensures |result| = |A| + 1 And result[|A|] = x
func Push(A []int, x int) (result []int) {
	return append(A, x)
}

// Counter counts up to a limit.
type Counter struct {
	n     int
	limit int
}

// NewCounter returns a counter nobody else has.
//
// @Ensures fresh(result) And result.n = 0 And result.limit = limit
func NewCounter(limit int) (result *Counter) {
	return &Counter{limit: limit}
}

// Inc advances the counter and leaves its limit alone.
//
// @Requires c != nil And c.n < c.limit
// @Modifies c.n
// @Ensures c.n' = c.n + 1
func (c *Counter) Inc() {
	c.n++
}

// Twice works on a counter through its methods' contracts.
//
// @Requires c != nil And c.n = 0 And c.limit = 10
// @Modifies c.n
// @Ensures c.n' = 2 And c.limit' = 10
func Twice(c *Counter) {
	c.Inc()
	c.Inc()
}

// SameOrNot writes through two pointers that may be one.
//
// @Requires a != nil And b != nil
// @Modifies a.n, b.n
// @Ensures result = 1
func SameOrNot(a, b *Counter) (result int) {
	a.n = 1
	b.n = 2
	return a.n // want `vego: postcondition may not hold: result = 1`
}

// Different says that they are not.
//
// @Requires a != nil And b != nil And a != b
// @Modifies a.n, b.n
// @Ensures result = 1
func Different(a, b *Counter) (result int) {
	a.n = 1
	b.n = 2
	return a.n
}

// Stack keeps a count that never exceeds what it holds.
//
// @Invariant 0 <= n <= |items|
type Stack struct {
	items []int
	n     int
}

// Top may index with n-1 because the invariant bounds n.
//
// @Requires s != nil And s.n > 0
// @Ensures result = s.items[s.n-1]
func (s *Stack) Top() (result int) {
	return s.items[s.n-1]
}

// Get reads a key that may be absent.
//
// @Ensures ok <-> has(m, k)
// @Ensures v = m[k]
func Get(m map[string]int, k string) (v int, ok bool) {
	v, ok = m[k]
	return v, ok
}

// Bump counts one more for a key.
//
// @Requires m != nil And m[k] < 1000
// @Modifies m
// @Ensures has(m', k) And m'[k] = m[k] + 1
func Bump(m map[string]int, k string) {
	m[k] = m[k] + 1
}

// Pair builds a map from two keys that may be equal.
//
// @Ensures True
func Pair(a, b int) (result map[int]int) {
	return map[int]int{a: 1, b: 2} // want `vego: the keys a and b of this map literal may be equal, and Go does not fix which of their entries the map keeps; build the map with assignments instead`
}

// ErrMissing and ErrEmpty are errors that are known not to be nil.
var (
	ErrMissing = errors.New("missing")
	ErrEmpty   = errors.New("empty")
	ErrRange   = errors.New("out of range")
)

// Head says when it succeeds and what it returns then.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures err = nil -> first = A[0]
func Head(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

// HeadWeak only says what success looks like.
//
// @Ensures err = nil -> first = A[0]
func HeadWeak(A []int) (first int, err error) { // want `vego: the contract of HeadWeak may also be met by a function that always returns an error.*`
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

// At makes an error that says what went wrong.
//
// @Ensures err = nil <-> 0 <= i < |A|
// @Ensures err = nil -> x = A[i]
func At(A []int, i int) (x int, err error) {
	if i < 0 || i >= len(A) {
		return 0, fmt.Errorf("index %d out of range", i)
	}
	return A[i], nil
}

// ParsePort relies on the contract that ships for strconv.Atoi.
//
// @Ensures err = nil -> 1 <= port <= 65535
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

// Peek says which error it returns, and when.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures err = ErrEmpty <-> |A| = 0
// @Ensures err = nil -> first = A[0]
func Peek(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

// PeekWhichOnly says which error it returns, but not when it succeeds.
//
// @Ensures err = ErrEmpty <-> |A| = 0
// @Ensures err = nil -> first = A[0]
func PeekWhichOnly(A []int) (first int, err error) { // want `vego: the contract of PeekWhichOnly may also be met by a function that always returns an error`
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

// EmptyRangeTrue claims the opposite for an empty slice.
//
// @Ensures |A| = 0 -> ranged
func EmptyRangeTrue(A []int) (ranged bool) {
	_, err := PeekLabelled(A)
	return errors.Is(err, ErrRange) // want `vego: postcondition may not hold: \|A\| = 0 -> ranged`
}

// EmptyRangeFull knows that the error is nil for a slice that is not empty.
//
// @Ensures |A| > 0 -> ~ranged
func EmptyRangeFull(A []int) (ranged bool) {
	_, err := PeekLabelled(A)
	return errors.Is(err, ErrRange)
}

// PeekOrZero compares the error with a package-level error variable.
//
// @Ensures v = 0 <-> (|A| = 0 Or A[0] = 0)
func PeekOrZero(A []int) (v int) {
	first, err := Peek(A)
	if err == ErrEmpty {
		return 0
	}
	return first
}

// Next returns io.EOF at the end of the string.
//
// @Requires 0 <= i
// @Ensures err = nil <-> i < |s|
// @Ensures err = io.EOF <-> i >= |s|
// @Ensures err = nil -> b = s[i]
func Next(s string, i int) (b byte, err error) {
	if i >= len(s) {
		return 0, io.EOF
	}
	return s[i], nil
}

// AtEnd compares with an error variable of another package.
//
// @Requires 0 <= i
// @Ensures end <-> i >= |s|
func AtEnd(s string, i int) (end bool) {
	_, err := Next(s, i)
	return err == io.EOF
}

// SameError compares two errors of which nothing is known.
//
// @Ensures True
func SameError(a, b error) (same bool) {
	return a == b // want `vego: cannot verify SameError: comparing two errors can panic when both hold the same uncomparable type; one of them must be nil, an error made by errors.New or fmt.Errorf or vouched for by a trusted contract, or a package-level error variable that holds such an error or a pointer, integer, string, or boolean, or an array or struct of these`
}

// PeekLabelled wraps the error of Peek, so that errors.Is still finds
// ErrEmpty in it.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures is(err, ErrEmpty) <-> |A| = 0
func PeekLabelled(A []int) (first int, err error) {
	first, err = Peek(A)
	if err != nil {
		return 0, fmt.Errorf("peek: %w", err)
	}
	return first, nil
}

// PeekLabelledWrong formats the error with %v, which does not wrap it.
//
// @Ensures err = nil <-> |A| > 0
// @Ensures is(err, ErrEmpty) <-> |A| = 0
func PeekLabelledWrong(A []int) (first int, err error) {
	first, err = Peek(A)
	if err != nil {
		return 0, fmt.Errorf("peek: %v", err) // want `vego: postcondition may not hold: is\(err, ErrEmpty\) <-> \|A\| = 0`
	}
	return first, nil
}

// Empty asks errors.Is about an error of known origin.
//
// @Ensures empty <-> |A| = 0
func Empty(A []int) (empty bool) {
	_, err := PeekLabelled(A)
	return errors.Is(err, ErrEmpty)
}

// EmptyRange asks about an error variable that the contract of
// PeekLabelled does not mention.
//
// @Ensures |A| = 0 -> ~ranged
func EmptyRange(A []int) (ranged bool) {
	_, err := PeekLabelled(A)
	return errors.Is(err, ErrRange) // want `vego: postcondition may not hold: \|A\| = 0 -> ~ranged`
}

// Lock is held or not.
type Lock struct{ taken bool }

// Acquire takes the lock.
//
// @Requires l != nil And ~l.taken
// @Modifies l
// @Ensures l.taken'
func (l *Lock) Acquire() {
	l.taken = true
}

// Release gives the lock back.
//
// @Requires l != nil And l.taken
// @Modifies l
// @Ensures ~l.taken'
func (l *Lock) Release() {
	l.taken = false
}

// Guarded gives the lock back on every way out.
//
// @Requires l != nil And ~l.taken And c != nil And c.n < c.limit
// @Modifies l, c.n
// @Ensures ~l.taken'
func Guarded(l *Lock, c *Counter, skip bool) {
	l.Acquire()
	defer l.Release()
	if skip {
		return
	}
	c.Inc()
}

// Pack puts two bytes into sixteen bits.
//
// @Ensures result = 256 * hi + lo
func Pack(hi, lo byte) (result uint16) {
	return uint16(hi)<<8 | uint16(lo)
}

// Join concatenates two strings of bounded length.
//
// @Requires |a| <= 1000 And |b| <= 1000
// @Ensures |result| = |a| + |b|
func Join(a, b string) (result string) {
	return a + b
}

// IsAdmin compares a string with a literal.
//
// @Ensures result <-> role = "admin"
func IsAdmin(role string) (result bool) {
	return role == "admin"
}

// SafeOnly has no contract to speak of; the annotation only asks for the
// checks every verified function gets.
//
// @Ensures True
func SafeOnly(A []int, i int) (result int) {
	if 0 <= i && i < len(A) {
		return A[i]
	}
	return 0
}

// CountPositive needs no name for the position, since its invariant does
// not speak of it.
//
// @Requires |A| <= 1000
// @Ensures 0 <= result
func CountPositive(A []int) (result int) {
	n := 0
	// @Invariant 0 <= n
	for _, x := range A {
		if x > 0 && n < 1000 {
			n++
		}
	}
	return n
}

// @Predicate digits(s) ::= Forall k in [0, |s|) : '0' <= s[k] <= '9'

// FirstDigit reads a digit from a string of digits.
//
// @Requires digits(s) And |s| > 0
// @Ensures 0 <= result <= 9
func FirstDigit(s string) (result int) {
	return int(s[0]) - 48
}

// @Predicate zeros(A, n) ::= n <= 0 Or (zeros(A, n-1) And A[n-1] = 0)

// LastZero unfolds a recursive predicate once.
//
// @Requires 0 < n <= |A| And zeros(A, n)
// @Ensures result = 0
func LastZero(A []int, n int) (result int) {
	return A[n-1]
}

// Push grows the slice the stack holds, so it lists both the struct, whose
// field it assigns, and the elements, which append may write. Its last
// clause tells a caller where the new slice lies.
//
// @Requires s != nil And s.n = |s.items| And s.n < 1000
// @Modifies s, s.items
// @Ensures s.n' = s.n + 1 And |s.items'| = s.n' And s.items'[s.n] = x
// @Ensures fresh(s.items) Or within(s.items', s.items)
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
	s.n++
}

// PushTwo can push again because it knows where the slice went.
//
// @Requires s != nil And s.n = |s.items| And s.n < 100
// @Modifies s, s.items
// @Ensures s.n' = s.n + 2
func PushTwo(s *Stack) {
	s.Push(1)
	s.Push(2)
}

// Pop changes the stack and returns a value.
//
// @Requires s != nil And s.n > 0
// @Modifies s.n
// @Ensures s.n' = s.n - 1 And result = s.items[s.n-1]
func (s *Stack) Pop() (result int) {
	s.n--
	return s.items[s.n]
}

// PopSum calls Pop twice in one expression. Go runs the two calls from
// left to right.
//
// @Requires s != nil And s.n > 1
// @Requires Forall k in [0, s.n) : 0 <= s.items[k] <= 1000
// @Modifies s.n
// @Ensures result = s.items[s.n-1] + s.items[s.n-2]
func PopSum(s *Stack) (result int) {
	return s.Pop() + s.Pop()
}

// PopInCondition calls Pop in the condition of an if.
//
// @Requires s != nil And s.n > 0
// @Modifies s.n
// @Ensures result <-> s.items[s.n-1] > 0
func PopInCondition(s *Stack) (result bool) {
	if s.Pop() > 0 {
		return true
	}
	return false
}

// PopIfAny pops only when the stack is not empty.
//
// @Requires s != nil
// @Modifies s.n
// @Ensures s.n = 0 -> s.n' = 0 And ~result
// @Ensures s.n > 0 -> s.n' = s.n - 1
func PopIfAny(s *Stack) (result bool) {
	return s.n > 0 && s.Pop() >= 0
}

// Iter counts up to n.
type Iter struct {
	i, n int
}

// Next advances the iterator if it can.
//
// @Requires it != nil And 0 <= it.i <= it.n
// @Modifies it.i
// @Ensures it.i < it.n -> it.i' = it.i + 1 And result
// @Ensures it.i = it.n -> it.i' = it.i And ~result
func (it *Iter) Next() (result bool) {
	if it.i < it.n {
		it.i++
		return true
	}
	return false
}

// Count advances the iterator in the condition of its loop.
//
// @Requires it != nil And it.i = 0 And 0 <= it.n < 1000
// @Modifies it.i
// @Ensures result = it.n And it.i' = it.n
func Count(it *Iter) (result int) {
	count := 0
	// @Invariant 0 <= it.i <= it.n And count = it.i
	// @Variant it.n - it.i
	for it.Next() {
		count++
	}
	return count
}

// Slot holds one number.
type Slot struct {
	v int
}

// value reads the number a slot holds.
//
// @Requires c != nil
// @Ensures result = c.v
func value(c *Slot) (result int) {
	return c.v
}

// Refill calls value in the target of an assignment whose append may write
// into the array of t.
//
// @Requires c != nil And 0 <= c.v < |rows| And |t| = 1
// @Modifies rows, t
func Refill(rows [][]int, t []int, c *Slot) {
	rows[value(c)] = append(t[:0], 5) // want `vego: cannot verify Refill: value is called in the target of this assignment, and Go may call it before or after append writes into the array of t\[:0\]; assign the result of value to a variable in a statement of its own first`
}

// RefillFirst assigns the result of value first.
//
// @Requires c != nil And 0 <= c.v < |rows| And |t| = 1
// @Modifies rows, t
// @Ensures rows'[c.v][0] = 5
func RefillFirst(rows [][]int, t []int, c *Slot) {
	i := value(c)
	rows[i] = append(t[:0], 5)
}

// five returns 5.
//
// @Ensures result = 5
func five() (result int) {
	return 5
}

// RefillOrdered has a call among the operands of append, which orders the
// append after value.
//
// @Requires c != nil And 0 <= c.v < |rows| And |t| = 1
// @Modifies rows, t
// @Ensures rows'[c.v][0] = 5
func RefillOrdered(rows [][]int, t []int, c *Slot) {
	rows[value(c)] = append(t[:0], five())
}

// PopAndCount reads s.n beside a call that changes it.
//
// @Requires s != nil And 0 < s.n < 1000
// @Requires Forall k in [0, s.n) : 0 <= s.items[k] <= 1000
// @Modifies s.n
func PopAndCount(s *Stack) (result int) {
	return s.n + s.Pop() // want `vego: s.n may be read before or after the call to Pop, which may change it, and Go does not fix the order; split the statement so that the order is the one you mean, as in n := s.n before it$`
}

// CountThenPop reads s.n in a statement of its own first.
//
// @Requires s != nil And 0 < s.n < 1000
// @Requires Forall k in [0, s.n) : 0 <= s.items[k] <= 1000
// @Modifies s.n
// @Ensures result = s.n + s.items[s.n-1]
func CountThenPop(s *Stack) (result int) {
	n := s.n
	return n + s.Pop()
}

// DrainForgets changes the stack in a loop, which forgets the invariant of
// the type along with everything else about what the loop changes.
//
// @Requires s != nil
// @Modifies s.n
func DrainForgets(s *Stack) {
	// @Variant s.n
	for s.n > 0 {
		s.Pop() // want `vego: invariant of Stack may not hold for what is passed to Pop as s: 0 <= n <= \|items\|`
	}
} // want `vego: invariant of Stack may not hold for s on return: 0 <= n <= \|items\|`

// Drain says it again in the invariant of the loop.
//
// @Requires s != nil
// @Modifies s.n
// @Ensures s.n' = 0
func Drain(s *Stack) {
	// @Invariant 0 <= s.n <= |s.items|
	// @Variant s.n
	for s.n > 0 {
		s.Pop()
	}
}

// Account holds money within a limit.
//
// @Invariant 0 <= balance <= 1000000
type Account struct {
	mu      sync.Mutex
	balance int
}

// TotalUnsaid adds up accounts reached through a slice, of which the
// invariant of the type is not known.
//
// @Requires |as| <= 100
// @Requires Forall k in [0, |as|) : as[k] != nil
func TotalUnsaid(as []*Account) (result int) {
	total := 0
	// @Invariant 0 <= total <= 1000000 * i
	for i := range as { // want `vego: loop invariant may not be preserved: 0 <= total <= 1000000 \* i`
		total += as[i].balance // want `vego: addition may overflow int`
	}
	return total
}

// Total states the bound for each element.
//
// @Requires |as| <= 100
// @Requires Forall k in [0, |as|) : as[k] != nil And 0 <= as[k].balance <= 1000000
// @Ensures 0 <= result <= 100000000
func Total(as []*Account) (result int) {
	total := 0
	// @Invariant 0 <= total <= 1000000 * i
	for i := range as {
		total += as[i].balance
	}
	return total
}

// Deposit adds n to the balance if the result stays within the limit.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu')
func (a *Account) Deposit(n int) (ok bool) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if n > 1000000-a.balance {
		return false
	}
	a.deposit(n)
	return true
}

// deposit runs while the caller holds the lock.
//
// @Requires a != nil And held(a.mu) And 0 <= n And a.balance + n <= 1000000
// @Modifies a.balance
// @Ensures a.balance' = a.balance + n
func (a *Account) deposit(n int) {
	a.balance += n
}

// DepositLocked takes the lock without saying that the caller does not
// hold it.
//
// @Requires a != nil And 0 <= n And a.balance + n <= 1000000
// @Modifies a
func (a *Account) DepositLocked(n int) {
	a.mu.Lock() // want `vego: precondition of Lock may not hold: ~held\(m\)`
	a.balance += n
	a.mu.Unlock()
}

// DepositSum adds n to the balance and says what the balance becomes.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu')
// @Ensures ok -> a.balance' = a.balance + n
func (a *Account) DepositSum(n int) (ok bool) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if n > 1000000-a.balance {
		return false
	}
	a.deposit(n)
	return true
}

// Settings is set up once.
type Settings struct {
	once sync.Once
	size int
}

// Setup sets the size the first time it is called.
//
// @Requires c != nil And ~running(c.once)
// @Modifies c.once, c.size
// @Ensures ~running(c.once')
func (c *Settings) Setup(n int) {
	c.once.Do(func() { c.size = n })
}

// SearchLocked locks the account in each call of the function that
// sort.Search calls.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu
// @Ensures True
func SearchLocked(a *Account, n int) (i int) {
	return sort.Search(n, func(k int) bool {
		a.mu.Lock() // want `vego: precondition of Lock may not hold: ~held\(m\), in the function literal run by sort.Search at guide.go:895:24`
		defer a.mu.Unlock()
		return k > 3
	})
}

// Switch locks only when on is set.
type Switch struct {
	mu sync.Mutex
	on bool
	n  int
}

// @Requires t != nil And ~held(t.mu)
// @Modifies t.mu, t.n
// @Ensures ~held(t.mu')
func (t *Switch) Step() {
	if t.on {
		t.mu.Lock()
	}
	t.n = 1
	if t.on {
		t.mu.Unlock()
	}
}

// @Requires a != nil And a.mu.mu.state = 0 // want `vego: in Requires annotation: a.mu.mu: mu is an unexported field of sync.Mutex, declared in package sync, and a formula in package guide cannot name it; sync.Mutex has the state held, which a formula names as held\(x\) for a value or a pointer x`
// @Ensures True
func Free(a *Account) {
}

// Snapshot copies the account, and its mutex with it.
//
// @Requires a != nil
// @Ensures True
func Snapshot(a *Account) (balance int) {
	b := *a // want `vego: cannot verify Snapshot: \*a copies a value of type Account, which holds a sync.Mutex; use a pointer to it; a value that holds a state, such as a sync.Mutex, must not be copied or overwritten, since its state changes only through its methods and sync documents that a Mutex must not be copied after first use`
	return b.balance
}

var ErrTooMany = errors.New("too many")

// ParseQuantity wraps the error of strconv.Atoi, whose contract vouches for
// it.
//
// @Requires |line| <= 1000
// @Ensures err = nil -> 0 <= n <= 1000
// @Ensures err = nil Or err = ErrTooMany Or is(err, strconv.ErrSyntax) Or is(err, strconv.ErrRange)
func ParseQuantity(line string) (n int, err error) {
	n, err = strconv.Atoi(line)
	if err != nil {
		return 0, fmt.Errorf("bad quantity %q: %w", line, err)
	}
	if n < 0 || n > 1000 {
		return 0, ErrTooMany
	}
	return n, nil
}

// Labelled formats an error that was passed in.
//
// @Ensures err != nil
func Labelled(cause error) (err error) {
	return fmt.Errorf("load: %w", cause) // want `vego: cannot verify Labelled: formatting cause would run the methods of an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, can be formatted`
}

// Nearest gives the int nearest to a number that does not fit in one.
//
// @Ensures err = nil Or is(err, strconv.ErrSyntax)
func Nearest(s string) (n int, err error) {
	n, err = strconv.Atoi(s)
	if errors.Is(err, strconv.ErrRange) {
		return n, nil
	}
	return n, err
}

// RemoveIfPresent removes a file, and does not fail when there is none.
//
// @Requires |name| <= 4096
// @Ensures ~is(err, os.ErrNotExist)
func RemoveIfPresent(name string) (err error) {
	err = os.Remove(name)
	if errors.Is(err, os.ErrNotExist) {
		return nil
	}
	return err
}

// LabelledOwn wraps an error of its own instead.
//
// @Ensures err != nil
func LabelledOwn() (err error) { // want `vego: the contract of LabelledOwn may also be met by a function that always returns an error`
	return fmt.Errorf("load: %w", ErrMissing)
}

// IsEmpty asks which error it is, which runs methods of the error that
// nobody has seen.
//
// @Ensures True
func IsEmpty(err error) (result bool) {
	return errors.Is(err, ErrEmpty) // want `vego: cannot verify IsEmpty: errors.Is would run the Is and Unwrap methods of err, an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, can be its first argument`
}

var calls int

// countCall changes calls, and is not verified.
func countCall() { calls++ }

// Counted reads a package-level variable that is changed.
//
// @Ensures True
func Counted() (result int) {
	return calls
}

// Clear removes the keys of the map it ranges over.
//
// @Modifies m
func Clear(m map[string]int) {
	for k := range m {
		delete(m, k)
	}
}

// Shift adds a key to the map it ranges over.
//
// @Requires m != nil And (Forall k in m : 0 <= k < 100)
// @Modifies m
func Shift(m map[int]int) {
	for k := range m {
		m[k+100] = m[k] // want `vego: this may add a key to m, the map that the loop at guide.go:1026:2 ranges over, and Go may or may not visit a key added during the loop; collect the new entries in another map and add them after the loop`
	}
}

// Unnamed has a result without a name, which its contract could not
// refer to.
//
// @Ensures True
func Unnamed(x int) int { // want `vego: Unnamed has annotations, so each of its results needs a name, as in func Unnamed\(x int\) \(i int\)`
	return x
}

// Find has a postcondition that runs over two lines.
//
// @Ensures result = -1 Or
// @   (0 <= result < |A| And A[result] = x)
func Find(A []int, x int) (result int) {
	// @Invariant Forall k in [0, i) : A[k] != x
	for i := range A {
		if A[i] == x {
			return i
		}
	}
	return -1
}

// DivideWrong is Divide with the loop condition that the README shows
// broken: the loop stops one step early when r = d.
//
// @Requires n >= 0 And d > 0
// @Ensures n = d*q + r And 0 <= r < d
func DivideWrong(n, d int) (q, r int) {
	q, r = 0, n
	// @Invariant n = d*q + r And 0 <= r
	// @Variant r
	for d < r {
		q, r = q+1, r-d
	}
	return q, r // want `vego: postcondition may not hold: 0 <= r < d`
}

// zero sets every element of A to zero.
//
// @Modifies A
// @Ensures Forall k in [0, |A|) : A'[k] = 0
func zero(A []int) {
	// @Invariant Forall k in [0, i) : A[k] = 0
	for i := range A {
		A[i] = 0
	}
}

// ZeroHeadWrong passes a slice that keeps the capacity of A, so zero may
// write all of A.
//
// @Requires |A| = 4
// @Modifies A
// @Ensures A'[3] = A[3]
func ZeroHeadWrong(A []int) {
	zero(A[:2])
} // want `vego: postcondition may not hold: A'\[3\] = A\[3\]`

// ZeroHead cuts the capacity, so the call cannot reach A[3].
//
// @Requires |A| = 4
// @Modifies A
// @Ensures A'[3] = A[3]
func ZeroHead(A []int) {
	zero(A[:2:2])
}

// Buffer holds the numbers that ClearCounted clears.
type Buffer struct {
	items []int
}

// ClearCountedWrong writes through b.items[i] in its loop, which makes the
// loop forget every []int the function may write, count included.
//
// @Requires b != nil
// @Modifies b.items
// @Ensures |result| = 1 And result[0] = |b.items|
func ClearCountedWrong(b *Buffer) (result []int) {
	count := make([]int, 1)
	count[0] = len(b.items)
	for i := range b.items {
		b.items[i] = 0
	}
	return count // want `vego: postcondition may not hold: result\[0\] = \|b.items\|`
}

// ClearCounted writes through a variable that the loop does not assign, so
// the loop forgets only what that variable refers to.
//
// @Requires b != nil
// @Modifies b.items
// @Ensures |result| = 1 And result[0] = |b.items|
func ClearCounted(b *Buffer) (result []int) {
	count := make([]int, 1)
	count[0] = len(b.items)
	items := b.items
	for i := range items {
		items[i] = 0
	}
	return count
}

// ClearCountedKept restates what the loop must keep as an invariant.
//
// @Requires b != nil
// @Modifies b.items
// @Ensures |result| = 1 And result[0] = |b.items|
func ClearCountedKept(b *Buffer) (result []int) {
	count := make([]int, 1)
	count[0] = len(b.items)
	// @Invariant count[0] = |b.items|
	for i := range b.items {
		b.items[i] = 0
	}
	return count
}

// CodeError is an error type of its own, which verified code cannot
// convert to error.
type CodeError struct{ code int }

func (e CodeError) Error() string { return "code " + strconv.Itoa(e.code) }

// AsError returns a CodeError as an error.
//
// @Ensures err != nil
func AsError() (err error) {
	return CodeError{code: 1} // want `vego: cannot verify AsError: converting a guide.CodeError to an error is not supported`
}
