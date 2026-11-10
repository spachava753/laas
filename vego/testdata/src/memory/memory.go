// Package memory holds programs that share memory: pointers to structs,
// methods, slices of one array, and appends. Each function either verifies
// or carries the defect its expectation names.
package memory

import "errors"

var errEmptyQueue = errors.New("empty queue")

// Counter counts up to a limit.
type Counter struct {
	n     int
	limit int
}

// NewCounter returns a counter nobody else has.
//
// @ Requires limit >= 0
func NewCounter(limit int) *Counter {
	return &Counter{limit: limit}
}

//@ Ensures fresh(result) And result.n = 0 And result.limit = limit

// Inc advances the counter, and says that the limit is left alone.
//
// @ Requires c != nil And c.n < c.limit And c.limit <= 1000
// @ Modifies c.n
func (c *Counter) Inc() {
	c.n++
}

//@ Ensures c.n' = c.n + 1

// Value reads the counter.
//
// @ Requires c != nil
func (c *Counter) Value() int {
	return c.n
}

//@ Ensures result = c.n

// NilReceiver forgets that the receiver may be nil.
//
// @ Requires c.n >= 0
func (c *Counter) NilReceiver() int {
	return c.n // want `vego: pointer may be nil`
}

// Twice calls a method that modifies its receiver.
//
// @ Requires c != nil And c.n = 0 And c.limit = 10
// @ Modifies c.n
func Twice(c *Counter) int {
	c.Inc()
	c.Inc()
	return c.Value()
}

//@ Ensures result = 2 And c.limit' = 10

// Undeclared writes a field without saying so.
//
// @ Requires c != nil
func Undeclared(c *Counter) {
	c.n = 0 // want `vego: c\.n is assigned, which Undeclared may not modify; list it in a //@ Modifies clause`
}

// TooMuch lists a field it never writes.
//
// @ Requires c != nil
// @ Modifies c.n, c.limit // want `vego: Modifies lists c\.limit, but TooMuch never needs to modify it`
func TooMuch(c *Counter) {
	c.n = 0
}

// WholeObject may write every field.
//
// @ Requires c != nil
// @ Modifies c
func WholeObject(c *Counter) {
	*c = Counter{n: 1, limit: 2}
}

//@ Ensures c.n' = 1 And c.limit' = 2

// CallerLosesField calls a function that may write c.n and still claims to
// know it.
//
// @ Requires c != nil And c.n = 0 And c.limit = 10
// @ Modifies c.n
func CallerLosesField(c *Counter) int {
	c.Inc()
	return c.n // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// SameOrDifferent must hold whether or not the two pointers are equal.
//
// @ Requires a != nil And b != nil
// @ Modifies a.n, b.n
func SameOrDifferent(a, b *Counter) int {
	a.n = 1
	b.n = 2
	return a.n // want `vego: postcondition may not hold: result = 1`
}

//@ Ensures result = 1

// Different says that they differ.
//
// @ Requires a != nil And b != nil And a != b
// @ Modifies a.n, b.n
func Different(a, b *Counter) int {
	a.n = 1
	b.n = 2
	return a.n
}

//@ Ensures result = 1

// FreshIsDifferent creates a counter, which cannot be the one passed in.
//
// @ Requires c != nil And c.n = 5
func FreshIsDifferent(c *Counter) int {
	d := NewCounter(3)
	d.Inc()
	return c.n + d.n
}

//@ Ensures result = 6

// NotFresh claims to return a new counter and returns its argument.
//
// @ Requires c != nil
func NotFresh(c *Counter) *Counter {
	return c // want `vego: postcondition may not hold: fresh\(result\)`
}

//@ Ensures fresh(result)

// Point is a struct used as a plain value.
type Point struct{ X, Y int }

// Mirror takes and returns a struct by value.
//
// @ Requires -1000 <= p.X <= 1000
func Mirror(p Point) Point {
	p.X = -p.X
	return p
}

//@ Ensures result.X = -p.X And result.Y = p.Y

// Copies shows that assigning a struct copies it.
func Copies() int {
	a := Point{X: 1, Y: 2}
	b := a
	b.X = 5
	return a.X + b.X
}

//@ Ensures result = 6

// Segment holds structs inside a struct.
type Segment struct {
	From, To Point
	Name     string
}

// Width reads through nested fields.
//
// @ Requires s != nil And 0 <= s.From.X <= s.To.X <= 1000
func Width(s *Segment) int {
	return s.To.X - s.From.X
}

//@ Ensures result >= 0

// Shift writes one nested field and leaves the rest alone.
//
// @ Requires s != nil And 0 <= s.From.X <= 1000
// @ Modifies s.From
func Shift(s *Segment) {
	s.From.X++
}

//@ Ensures s.From.X' = s.From.X + 1 And s.From.Y' = s.From.Y

// ShiftKeeps relies on what Shift leaves alone.
//
// @ Requires s != nil And s.From.X = 0 And s.To.X = 7
// @ Modifies s.From
func ShiftKeeps(s *Segment) int {
	Shift(s)
	return s.To.X + s.From.X
}

//@ Ensures result = 8

// Stack is a slice inside a struct.
type Stack struct {
	items []int
}

// Push appends to the stack, which may write into the capacity of its slice
// or move it to a new array.
//
// @ Requires s != nil And |s.items| < 1000
// @ Modifies s, s.items
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
}

//@ Ensures |s.items'| = |s.items| + 1 And s.items'[|s.items|] = x
//@ Ensures Forall k in [0, |s.items|) : s.items'[k] = s.items[k]
//@ Ensures fresh(s.items) Or within(s.items', s.items)

// Top reads the last element.
//
// @ Requires s != nil And |s.items| > 0
func (s *Stack) Top() int {
	return s.items[len(s.items)-1]
}

//@ Ensures result = s.items[|s.items| - 1]

// PushThenTop uses both.
//
// @ Requires s != nil And |s.items| = 0
// @ Modifies s, s.items
func PushThenTop(s *Stack) int {
	s.Push(4)
	s.Push(9)
	return s.Top()
}

//@ Ensures result = 9 And |s.items'| = 2 And s.items'[0] = 4
//@ Ensures fresh(s.items) Or within(s.items', s.items)

// Clear writes the elements but not the field.
//
// @ Requires s != nil
// @ Modifies s.items
func (s *Stack) Clear() {
	//@ Invariant Forall k in [0, i) : s.items[k] = 0
	for i := range s.items {
		s.items[i] = 0
	}
}

//@ Ensures |s.items'| = |s.items| And Forall k in [0, |s.items|) : s.items'[k] = 0

// Shared shows two names for one array.
//
// @ Requires |A| > 0
// @ Modifies A
func Shared(A []int) int {
	B := A
	B[0] = 1
	return A[0]
}

//@ Ensures result = 1 And A'[0] = 1

// Tail returns a slice of the same array.
//
// @ Requires |A| > 1
func Tail(A []int) int {
	B := A[1:]
	return B[0]
}

//@ Ensures result = A[1]

// Halves writes through two slices of one array.
//
// @ Requires |A| = 4
// @ Modifies A
func Halves(A []int) {
	left, right := A[:2], A[2:]
	left[0] = 1
	right[0] = 2
}

//@ Ensures A'[0] = 1 And A'[2] = 2 And A'[1] = A[1] And A'[3] = A[3]

// OutOfCapacity slices beyond the capacity.
//
// @ Requires |A| = 4
func OutOfCapacity(A []int) int {
	B := A[1:3]
	C := B[0:4] // want `vego: slice bounds may be out of range`
	return len(C)
}

// zero clears a slice.
//
// @ Modifies A
func zero(A []int) {
	//@ Invariant Forall k in [0, i) : A[k] = 0
	for i := range A {
		A[i] = 0
	}
}

//@ Ensures Forall k in [0, |A|) : A'[k] = 0

// ZeroFront clears the first half and keeps the second. The capacity of the
// first half is cut off, since zero may write all of it.
//
// @ Requires |A| = 4 And A[3] = 7
// @ Modifies A
func ZeroFront(A []int) int {
	zero(A[:2:2])
	return A[0] + A[3]
}

//@ Ensures result = 7

// ZeroFrontLoose leaves the capacity, so the call may write the second half.
//
// @ Requires |A| = 4 And A[3] = 7
// @ Modifies A
func ZeroFrontLoose(A []int) int {
	zero(A[:2])
	return A[0] + A[3] // want `vego: postcondition may not hold: result = 7`
}

//@ Ensures result = 7

// copyInto copies src to dst, which must not overlap.
//
// @ Requires |dst| = |src|
// @ Modifies dst
func copyInto(dst, src []int) {
	//@ Invariant Forall k in [0, i) : dst[k] = src[k]
	for i := range src {
		dst[i] = src[i]
	}
}

//@ Ensures Forall k in [0, |src|) : dst'[k] = src[k]

// Overlapping passes one array twice.
//
// @ Requires |A| = 4
// @ Modifies A
func Overlapping(A []int) {
	copyInto(A[:2], A[2:]) // want `vego: the slices passed to copyInto as dst and src may overlap`
}

// Disjoint passes two separate stretches.
//
// @ Requires |A| = 4
// @ Modifies A
func Disjoint(A []int) {
	copyInto(A[:2:2], A[2:])
}

//@ Ensures A'[0] = A[2] And A'[1] = A[3] And A'[2] = A[2]

// Doubled builds a new slice while reading another.
//
// @ Requires Forall k in [0, |A|) : -1000 <= A[k] <= 1000
func Doubled(A []int) (R []int) {
	//@ Invariant |R| = i And Forall k in [0, i) : R[k] = 2 * A[k]
	for i := range A {
		R = append(R, 2*A[i])
	}
	return R
}

//@ Ensures fresh(R) And |R| = |A| And Forall k in [0, |A|) : R[k] = 2 * A[k]

// AppendsToParameter may write into the caller's array without saying so.
//
// @ Requires |A| < 1000
func AppendsToParameter(A []int) []int {
	return append(A, 1) // want `vego: append may write into the capacity of A, which AppendsToParameter may not modify; list it in a //@ Modifies clause`
}

// AppendsDeclared says so.
//
// @ Requires |A| < 1000
// @ Modifies A
func AppendsDeclared(A []int) []int {
	return append(A, 1)
}

//@ Ensures |result| = |A| + 1 And result[|A|] = 1

// AppendAliases shows that an append may or may not share the array.
func AppendAliases() int {
	a := make([]int, 1, 2)
	b := append(a, 5)
	b[0] = 3
	return a[0]
}

//@ Ensures result = 3

// AppendCopies appends beyond the capacity, which copies.
func AppendCopies() int {
	a := make([]int, 1)
	b := append(a, 5)
	b[0] = 3
	return a[0]
}

//@ Ensures result = 0

// NilSlice tells a nil slice from an empty one.
func NilSlice() bool {
	var a []int
	b := make([]int, 0)
	return a == nil && b != nil
}

//@ Ensures result

// Grid is a slice of slices.
//
// @ Requires |rows| > 1 And |rows[0]| > 0 And |rows[1]| > 0
// @ Requires rows[1][0] = 5
func Grid(rows [][]int) int {
	return rows[1][0]
}

//@ Ensures result = 5

// Sum adds up the X of a slice of structs.
//
// @ Requires Forall k in [0, |ps|) : 0 <= ps[k].X <= 100
// @ Requires |ps| <= 1000
func Sum(ps []Point) (s int) {
	//@ Invariant 0 <= s <= 100 * i
	for i := range ps {
		s += ps[i].X
	}
	return s
}

//@ Ensures 0 <= s <= 100 * |ps|

// SetAll writes one field of every element.
//
// @ Modifies ps
func SetAll(ps []Point) {
	//@ Invariant Forall k in [0, i) : ps[k].X = 1
	//@ Invariant Forall k in [0, |ps|) : ps[k].Y = old(ps[k].Y)
	for i := range ps {
		ps[i].X = 1
	}
}

//@ Ensures Forall k in [0, |ps|) : ps'[k].X = 1 And ps'[k].Y = ps[k].Y

// AddressOfLocal is outside the fragment.
func AddressOfLocal() int {
	x := Point{}
	p := &x // want `vego: cannot verify AddressOfLocal: taking the address of x is not supported; only &T\{\.\.\.\} creates a pointer`
	return p.X
}

//@ Ensures result = 0

// Interior is outside the fragment too.
//
// @ Requires s != nil
func Interior(s *Segment) int {
	p := &s.From // want `vego: cannot verify Interior: taking the address of s\.From is not supported; only &T\{\.\.\.\} creates a pointer`
	return p.X
}

// ModifiesValue lists something the caller cannot see.
//
// @ Modifies p.X // want `vego: in Modifies annotation: p\.X is passed by value, so the caller cannot see a change to it`
func ModifiesValue(p Point) {
	p.X = 1
}

// PrimedValue primes a field of a value.
func PrimedValue(p Point) int {
	return p.X
}

//@ Ensures result = p.X' // want `vego: in Ensures annotation: p is passed by value, so only its value on entry is visible to callers; drop the prime`

// LoopKeeps writes one counter in a loop and reads another afterwards.
//
// @ Requires a != nil And b != nil And a != b And b.n = 3 And 0 <= n <= 100
// @ Modifies a.n
func LoopKeeps(a, b *Counter, n int) int {
	a.n = 0
	//@ Invariant a.n = i And 0 <= i <= n
	//@ Variant n - i
	for i := 0; i < n; i++ {
		a.n++
	}
	return a.n + b.n
}

//@ Ensures result = n + 3

// LoopKeepsSlices fills one slice in a loop and still knows the other.
//
// @ Requires |A| = |B| And |A| > 0 And B[0] = 4
// @ Modifies A
func LoopKeepsSlices(A, B []int) int {
	//@ Invariant Forall k in [0, i) : A[k] = 0
	for i := range A {
		A[i] = 0
	}
	return A[0] + B[0]
}

//@ Ensures result = 4

// Log stands for a type whose methods are not verified.
type Log struct {
	count int
	sink  func(string)
}

func (l *Log) Write(text string) (err error) { l.count++; l.sink(text); return nil }
func (l *Log) Count() int                    { return l.count }
func newLog() *Log                           { return &Log{} }
func grab(l *Log)                            {}

// WritesTwice relies on the trusted contracts of two methods.
func WritesTwice() (n int, err error) {
	l := newLog()
	err = l.Write("a")
	if err != nil {
		return 0, err
	}
	err = l.Write("b")
	if err != nil {
		return 0, err
	}
	return l.Count(), nil
}

//@ Ensures err = nil -> n = 2

// WritesForgets claims the count survives a call that may change it.
//
// @ Requires l != nil And l.count = 0
// @ Modifies l
func WritesForgets(l *Log) int {
	_ = l.Write("a")
	return l.count // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// WritesUndeclared calls a trusted method that modifies its receiver.
//
// @ Requires l != nil
func WritesUndeclared(l *Log) {
	_ = l.Write("a") // want `vego: Write may modify l, which WritesUndeclared may not modify; list it in a //@ Modifies clause`
}

// Grabs uses a trusted contract whose modifies cannot be read.
//
// @ Requires l != nil
func Grabs(l *Log) {
	grab(l) // want `vego: the trusted contract of memory.grab \(trusted.yaml:\d+\) cannot be used: in its modifies "l.missing": l\.missing: memory.Log has no field missing` `vego: cannot verify Grabs: grab has a contract that could not be understood`
}

// Queue has operations that fail for reasons its fields decide.
type Queue struct {
	items []int
	max   int
}

// Pop removes the last element and fails on an empty queue, which is a
// condition on what the receiver points to.
//
// @ Requires q != nil
// @ Modifies q
func (q *Queue) Pop() (x int, err error) {
	if len(q.items) == 0 {
		return 0, errEmptyQueue
	}
	x = q.items[len(q.items)-1]
	q.items = q.items[:len(q.items)-1]
	return x, nil
}

//@ Ensures err = nil <-> |q.items| > 0
//@ Ensures err = nil -> x = q.items[|q.items| - 1] And |q.items'| = |q.items| - 1

// PopAlwaysFails never says when it succeeds.
//
// @ Requires q != nil
func (q *Queue) PopAlwaysFails() (x int, err error) { // want `vego: the contract of PopAlwaysFails would also be met by a function that always returns an error`
	if len(q.items) == 0 {
		return 0, errEmptyQueue
	}
	return q.items[0], nil
}

//@ Ensures err = nil -> x = q.items[0]

// Full succeeds when a field allows.
//
// @ Requires q != nil
func (q *Queue) Full() (err error) {
	if q.max <= 0 {
		return errEmptyQueue
	}
	return nil
}

//@ Ensures err = nil <-> q.max > 0

// Pair holds two pointers.
type Pair struct {
	left, right *Counter
}

// NilField follows a pointer read from memory without knowing it is not nil.
//
// @ Requires p != nil
func NilField(p *Pair) int {
	return p.left.n // want `vego: pointer may be nil`
}

// BothFields reads through two pointers that may be the same.
//
// @ Requires p != nil And p.left != nil And p.right != nil
// @ Modifies p.left.n
func BothFields(p *Pair) int {
	p.left.n = 0
	return p.right.n // want `vego: postcondition may not hold: result = p\.right\.n`
}

//@ Ensures result = p.right.n

// BothFieldsApart says that they differ.
//
// @ Requires p != nil And p.left != nil And p.right != nil And p.left != p.right
// @ Modifies p.left.n
func BothFieldsApart(p *Pair) int {
	p.left.n = 0
	return p.right.n
}

//@ Ensures result = p.right.n

// SwapFields exchanges two pointers and keeps what they point to.
//
// @ Requires p != nil
// @ Modifies p
func SwapFields(p *Pair) {
	p.left, p.right = p.right, p.left
}

//@ Ensures p.left' = p.right And p.right' = p.left

// Empty has no size, so two of them need not be distinct.
type Empty struct{}

// EmptiesDiffer compares pointers that Go does not promise to differ.
func EmptiesDiffer() bool {
	a, b := &Empty{}, &Empty{}
	return a != b // want `vego: cannot verify EmptiesDiffer: pointers to values of size zero may or may not be equal, so comparing them is not supported`
}

//@ Ensures result

// NewDiffer compares two new objects with a size.
func NewDiffer() bool {
	a, b := &Counter{}, new(Counter)
	return a != b && a != nil
}

//@ Ensures result

// AliasInLoop writes through one slice in a loop and claims another view of
// the same array is unchanged.
//
// @ Requires |A| = 4
// @ Modifies A
func AliasInLoop(A []int) int {
	B := A[2:]
	//@ Invariant True
	for i := range A {
		A[i] = 0
	}
	return B[0] // want `vego: postcondition may not hold: result = A\[2\]`
}

//@ Ensures result = A[2]

// CalleeAlias passes an alias to a function that writes it.
//
// @ Requires |A| = 4 And A[0] = 7
// @ Modifies A
func CalleeAlias(A []int) int {
	B := A[:2:2]
	zero(B)
	return A[0] // want `vego: postcondition may not hold: result = 7`
}

//@ Ensures result = 7

// AppendMayAlias assumes an append copied.
//
// @ Requires |A| > 0 And |A| < 1000 And A[0] = 7
// @ Modifies A
func AppendMayAlias(A []int) int {
	B := append(A, 1)
	B[0] = 3
	return A[0] // want `vego: postcondition may not hold: result = 7`
}

//@ Ensures result = 7

// BytesCapacity assumes the copy has no spare capacity.
//
// @ Requires |s| = 2
func BytesCapacity(s string) int {
	b := []byte(s)
	c := append(b, 1)
	d := append(b, 2)
	return int(c[2]) - int(d[2]) + int(d[2]) // want `vego: postcondition may not hold: result = 1`
}

//@ Ensures result = 1

// Pointers is a slice of pointers.
//
// @ Requires |cs| = 2 And cs[0] != nil And cs[1] != nil And cs[0] != cs[1]
// @ Requires cs[1].n = 4
// @ Modifies cs[0]
func Pointers(cs []*Counter) int {
	cs[0].n = 1
	return cs[0].n + cs[1].n
}

//@ Ensures result = 5

// RangeSeesWrites reads each element as it is when its turn comes.
//
// @ Requires |A| = 2
// @ Modifies A
func RangeSeesWrites(A []int) (s int) {
	A[0], A[1] = 1, 1
	//@ Invariant (i = 0 -> s = 0 And A[0] = 1 And A[1] = 1) And (i = 1 -> s = 1 And A[1] = 5) And (i = 2 -> s = 6)
	for i, x := range A {
		s += x
		if i == 0 {
			A[1] = 5
		}
	}
	return s
}

//@ Ensures s = 6

// UnusedSlice lists a slice it only reads.
//
// @ Requires |A| > 0 And |B| > 0
// @ Modifies A, B // want `vego: Modifies lists B, but UnusedSlice never needs to modify it`
func UnusedSlice(A, B []int) {
	A[0] = B[0]
}

// CopyOfStruct shows that a struct read through a pointer is a copy.
//
// @ Requires c != nil And c.n = 1
// @ Modifies c
func CopyOfStruct(c *Counter) int {
	saved := *c
	c.n = 2
	return saved.n + c.n
}

//@ Ensures result = 3

// ValueReceiver gets a copy of the struct, so the caller's is untouched.
func (p Point) Moved() Point {
	p.X = p.X + 0
	p.Y = 0
	return p
}

//@ Ensures result.X = p.X And result.Y = 0

// CallsValueReceiver calls it through a pointer.
//
// @ Requires p != nil And p.Y = 3
func CallsValueReceiver(p *Point) int {
	q := p.Moved()
	return q.Y + p.Y
}

//@ Ensures result = 3

// FreshParameter says a parameter is new.
func FreshParameter(c *Counter) {}

//@ Ensures fresh(c) // want `vego: in Ensures annotation: fresh\(c\): c was passed in, so the call did not create it`

// OneElement lists a single element of a slice of structs.
//
// @ Requires |ps| > 0
// @ Modifies ps[0] // want `vego: in Modifies annotation: ps\[0\] is a single element or part of one; list the slice instead`
func OneElement(ps []Point) {
	ps[0].X = 1
}

// OtherPointer writes through a pointer it did not list.
//
// @ Requires |cs| = 2 And cs[0] != nil And cs[1] != nil
// @ Modifies cs[0]
func OtherPointer(cs []*Counter) {
	cs[0].n = 1
	cs[1].n = 1 // want `vego: cs\[1\]\.n is assigned, which OtherPointer may not modify; list it in a //@ Modifies clause`
}

// Lexer reads a string byte by byte.
type Lexer struct {
	input string
	pos   int
}

// Next returns the next byte, if there is one.
//
// @ Requires l != nil And 0 <= l.pos <= |l.input|
// @ Modifies l.pos
func (l *Lexer) Next() (c byte, ok bool) {
	if l.pos >= len(l.input) {
		return 0, false
	}
	c = l.input[l.pos]
	l.pos++
	return c, true
}

//@ Ensures 0 <= l.pos' <= |l.input|
//@ Ensures ok -> l.pos' = l.pos + 1 And c = l.input[l.pos]
//@ Ensures ~ok -> l.pos' = l.pos And l.pos = |l.input|

// CountDigits drives the lexer to the end of its input in a loop that is
// only left by break.
//
// @ Requires l != nil And l.pos = 0
// @ Modifies l.pos
func CountDigits(l *Lexer) (n int) {
	//@ Invariant 0 <= l.pos <= |l.input| And 0 <= n <= l.pos
	//@ Variant |l.input| - l.pos
	for {
		c, ok := l.Next()
		if !ok {
			break
		}
		if c >= '0' && c <= '9' {
			n++
		}
	}
	return n
}

//@ Ensures 0 <= n <= |l.input|

// Ring is a buffer that wraps around.
type Ring struct {
	buf        []int
	head, size int
}

// Put writes behind the last element.
//
// @ Requires r != nil And 0 < |r.buf| <= 1000000 And 0 <= r.head < |r.buf| And 0 <= r.size < |r.buf|
// @ Modifies r.size, r.buf
func (r *Ring) Put(x int) {
	r.buf[(r.head+r.size)%len(r.buf)] = x
	r.size++
}

//@ Ensures r.size' = r.size + 1 And r.buf'[(r.head + r.size) % |r.buf|] = x

// NewRing returns a ring nobody else has, with an array nobody else has.
//
// @ Requires n >= 0 And n <= 1000
func NewRing(n int) *Ring {
	return &Ring{buf: make([]int, n+1)}
}

//@ Ensures fresh(result) And fresh(result.buf) And |result.buf| = n + 1 And result.size = 0 And result.head = 0

// UseRing may write the ring because it is new.
func UseRing() int {
	r := NewRing(4)
	r.Put(7)
	r.Put(8)
	return r.size
}

//@ Ensures result = 2

// Config is validated field by field.
type Config struct {
	Name    string
	Retries int
	Tags    []string
}

// Valid says exactly when it succeeds, in terms of what c points to.
//
// @ Requires c != nil
func (c *Config) Valid() (err error) {
	if c.Name == "" {
		return errEmptyQueue
	}
	if c.Retries < 0 || c.Retries > 10 {
		return errEmptyQueue
	}
	return nil
}

//@ Ensures err = nil <-> (|c.Name| > 0 And 0 <= c.Retries <= 10)

// UseRingForgets claims a size the calls changed.
func UseRingForgets() int {
	r := NewRing(4)
	r.Put(7)
	return r.size // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// PutFull forgets that the ring may be full.
//
// @ Requires r != nil And 0 < |r.buf| <= 1000000 And 0 <= r.head < |r.buf| And 0 <= r.size <= |r.buf|
// @ Modifies r.size, r.buf
func (r *Ring) PutFull(x int) {
	r.buf[r.head+r.size] = x // want `vego: index may be out of range`
	r.size++
}

// Renamed is Counter under another name: the same type, and the same memory.
type Renamed = Counter

// AliasedType writes through one spelling of a type and reads through the
// other.
//
// @ Requires p != nil And q = p And p.n = 0
// @ Modifies q.n
func AliasedType(p *Counter, q *Renamed) int {
	q.n = 1
	return p.n // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// ByteIsUint8 converts between two spellings of one slice type, which shares
// the array.
func ByteIsUint8() byte {
	a := []byte{0}
	b := []uint8(a)
	b[0] = 1
	return a[0] // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// Partly has a field that is not modelled.
type Partly struct {
	X int
	C chan int
}

// ComparesPartly compares structs whose unmodelled fields may differ.
//
// @ Requires a.X = b.X
func ComparesPartly(a, b Partly) bool {
	return a == b // want `vego: cannot verify ComparesPartly: a value of type memory.Partly cannot be used here`
}

//@ Ensures result = True

// ReadsPartly uses the modelled field of such a struct.
func ReadsPartly(a Partly) int {
	return a.X
}

//@ Ensures result = a.X

// AppendInInit appends in the initializer of an if statement.
func AppendInInit() int {
	s := []int{}
	if s = append(s, 1); len(s) == 0 {
		return 0
	}
	return 1 // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// AppendInPost appends in the post statement of a loop.
func AppendInPost() int {
	var s []int
	//@ Invariant |s| = i And 0 <= i <= 3
	//@ Variant 3 - i
	for i := 0; i < 3; s = append(s, i) {
		i++
	}
	return len(s)
}

//@ Ensures result = 3

// NamedBrk has a parameter with the name the verifier uses for the bound of
// memory.
func NamedBrk(brk *Counter) int {
	return brk.n // want `vego: pointer may be nil`
}

//@ Ensures True

// NewFromValue uses new with a value to start from.
func NewFromValue() int {
	p := new(Counter{n: 1})
	return p.n // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// NewFromNil evaluates the value it starts from.
func NewFromNil(p *Counter) *Counter {
	return new(*p) // want `vego: pointer may be nil`
}

//@ Ensures True

// MovedCapacity looks into the capacity of an array that append created.
// Nothing is known about it; in particular it does not hold what followed
// the old elements in the old array.
func MovedCapacity() byte {
	a := []byte{0, 0, 7}
	b := append(a[:1:1], 1)
	if cap(b) > 2 {
		c := b[:cap(b)]
		return c[2] // want `vego: postcondition may not hold: result = 7`
	}
	return 7
}

//@ Ensures result = 7

// MovedElements keeps the elements that were copied.
func MovedElements() int {
	a := []int{4, 5, 6}
	b := append(a[:2:2], 9)
	return b[0] + b[1] + b[2]
}

//@ Ensures result = 18

// Users is a slice of structs whose contract says when a search succeeds.
type Users struct {
	list []Point
}

// FindX succeeds exactly when some element has the X asked for, which is a
// condition a sample slice of structs has to meet.
//
// @ Requires u != nil
func (u *Users) FindX(x int) (index int, err error) {
	//@ Invariant Forall k in [0, i) : u.list[k].X != x
	for i := range u.list {
		if u.list[i].X == x {
			return i, nil
		}
	}
	return -1, errEmptyQueue
}

//@ Ensures err = nil <-> Exists k in [0, |u.list|) : u.list[k].X = x

// TagsShare converts a slice between struct types that differ in a tag,
// which keeps the array. The two types have memory of their own in the
// model, so the conversion is not accepted.
func TagsShare() int {
	a := []struct {
		X int `a:"1"`
	}{{X: 0}}
	b := []struct { // want `vego: cannot verify TagsShare: converting a .* is not supported`
		X int `b:"1"`
	}(a)
	b[0].X = 1
	return a[0].X
}

//@ Ensures result = 0

// Number is int under another name.
type Number = int

// SpellingsShare converts between two spellings of one struct type, which
// differ inside a field that is not modelled.
func SpellingsShare() int {
	a := []struct {
		X int
		C [1]Number
	}{{X: 0}}
	b := []struct {
		X int
		C [1]int
	}(a)
	b[0].X = 1
	return a[0].X // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// Small is a struct whose field has a narrow type.
type Small struct{ X byte }

func readySmall(a []Small) error { return nil }

// makeSmall returns a slice too long for a sample.
func makeSmall() []Small {
	return make([]Small, 65)
}

//@ Ensures |result| = 65

// AlwaysFailsAfterReadySmall calls a function that succeeds whenever every
// field holds a value of its type, which is always.
func AlwaysFailsAfterReadySmall() error { // want `vego: the contract of AlwaysFailsAfterReadySmall would also be met by a function that always returns an error`
	a := makeSmall()
	_ = readySmall(a)
	return errEmptyQueue
}

//@ Ensures True

// One is a struct with a single field, which is still not a single value.
type One struct{ X int }

// WholeSlice compares slices of structs as wholes, which has no meaning in
// an annotation.
//
// @ Requires |a| = 1 And a[0].X = 0
// @ Modifies a
func WholeSlice(a []One) {
	a[0].X = 1
}

//@ Ensures a' = a // want `vego: in Ensures annotation: a is a slice of memory.One; index it and name a field`

// TaggedA and TaggedB differ only in the tag of what their slices hold.
type TaggedA struct {
	Items []struct {
		X int `a:"1"`
	}
}

// TaggedB is TaggedA with another tag.
type TaggedB struct {
	Items []struct {
		X int `b:"1"`
	}
}

// StructTagsShare converts a struct whose slice would change its memory.
func StructTagsShare(a TaggedA) int {
	b := TaggedB(a) // want `vego: cannot verify StructTagsShare: converting a memory.TaggedA to a memory.TaggedB is not supported`
	return len(b.Items)
}

//@ Ensures result >= 0

// Blob holds bytes behind a pointer, and Named a string in each element.
type Blob struct{ B []byte }

// Named holds a string.
type Named struct{ S string }

func readyBlob(p *Blob) error    { return nil }
func readyNamed(a []Named) error { return nil }

func makeBlob() *Blob {
	return &Blob{B: make([]byte, 65)}
}

//@ Ensures fresh(result) And |result.B| = 65

func makeNamed() []Named {
	return make([]Named, 65)
}

//@ Ensures |result| = 65

// AlwaysFailsAfterReadyBlob calls a function that succeeds whenever the
// bytes behind its pointer are bytes.
func AlwaysFailsAfterReadyBlob() error { // want `vego: the contract of AlwaysFailsAfterReadyBlob would also be met by a function that always returns an error`
	p := makeBlob()
	_ = readyBlob(p)
	return errEmptyQueue
}

//@ Ensures True

// AlwaysFailsAfterReadyNamed calls one that succeeds whenever the bytes of
// the strings in its elements are bytes.
func AlwaysFailsAfterReadyNamed() error { // want `vego: the contract of AlwaysFailsAfterReadyNamed would also be met by a function that always returns an error`
	a := makeNamed()
	_ = readyNamed(a)
	return errEmptyQueue
}

//@ Ensures True

func readyRows(a [][]byte) error { return nil }

func makeRows() [][]byte {
	return make([][]byte, 65)
}

//@ Ensures |result| = 65

// AlwaysFailsAfterReadyRows calls a function that succeeds whenever the
// slices in its slice have lengths that are not negative.
func AlwaysFailsAfterReadyRows() error { // want `vego: the contract of AlwaysFailsAfterReadyRows would also be met by a function that always returns an error`
	a := makeRows()
	_ = readyRows(a)
	return errEmptyQueue
}

//@ Ensures True
