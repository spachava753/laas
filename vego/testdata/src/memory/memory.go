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
// @ Ensures fresh(result) And result.n = 0 And result.limit = limit
func NewCounter(limit int) (result *Counter) {
	return &Counter{limit: limit}
}

// Inc advances the counter, and says that the limit is left alone.
//
// @ Requires c != nil And c.n < c.limit And c.limit <= 1000
// @ Modifies c.n
// @ Ensures c.n' = c.n + 1
func (c *Counter) Inc() {
	c.n++
}

// Value reads the counter.
//
// @ Requires c != nil
// @ Ensures result = c.n
func (c *Counter) Value() (result int) {
	return c.n
}

// NilReceiver forgets that the receiver may be nil.
//
// @ Requires c.n >= 0
func (c *Counter) NilReceiver() (result int) {
	return c.n // want `vego: pointer may be nil`
}

// Twice calls a method that modifies its receiver.
//
// @ Requires c != nil And c.n = 0 And c.limit = 10
// @ Modifies c.n
// @ Ensures result = 2 And c.limit' = 10
func Twice(c *Counter) (result int) {
	c.Inc()
	c.Inc()
	return c.Value()
}

// Undeclared writes a field without saying so.
//
// @ Requires c != nil
func Undeclared(c *Counter) {
	c.n = 0 // want `vego: c\.n is assigned, which Undeclared may not modify; list it in a // @ Modifies clause`
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
// @ Ensures c.n' = 1 And c.limit' = 2
func WholeObject(c *Counter) {
	*c = Counter{n: 1, limit: 2}
}

// CallerLosesField calls a function that may write c.n and still claims to
// know it.
//
// @ Requires c != nil And c.n = 0 And c.limit = 10
// @ Modifies c.n
// @ Ensures result = 0
func CallerLosesField(c *Counter) (result int) {
	c.Inc()
	return c.n // want `vego: postcondition may not hold: result = 0`
}

// SameOrDifferent must hold whether or not the two pointers are equal.
//
// @ Requires a != nil And b != nil
// @ Modifies a.n, b.n
// @ Ensures result = 1
func SameOrDifferent(a, b *Counter) (result int) {
	a.n = 1
	b.n = 2
	return a.n // want `vego: postcondition may not hold: result = 1`
}

// Different says that they differ.
//
// @ Requires a != nil And b != nil And a != b
// @ Modifies a.n, b.n
// @ Ensures result = 1
func Different(a, b *Counter) (result int) {
	a.n = 1
	b.n = 2
	return a.n
}

// FreshIsDifferent creates a counter, which cannot be the one passed in.
//
// @ Requires c != nil And c.n = 5
// @ Ensures result = 6
func FreshIsDifferent(c *Counter) (result int) {
	d := NewCounter(3)
	d.Inc()
	return c.n + d.n
}

// NotFresh claims to return a new counter and returns its argument.
//
// @ Requires c != nil
// @ Ensures fresh(result)
func NotFresh(c *Counter) (result *Counter) {
	return c // want `vego: postcondition may not hold: fresh\(result\)`
}

// Point is a struct used as a plain value.
type Point struct{ X, Y int }

// Mirror takes and returns a struct by value.
//
// @ Requires -1000 <= p.X <= 1000
// @ Ensures result.X = -p.X And result.Y = p.Y
func Mirror(p Point) (result Point) {
	p.X = -p.X
	return p
}

// Copies shows that assigning a struct copies it.
//
// @ Ensures result = 6
func Copies() (result int) {
	a := Point{X: 1, Y: 2}
	b := a
	b.X = 5
	return a.X + b.X
}

// Segment holds structs inside a struct.
type Segment struct {
	From, To Point
	Name     string
}

// Width reads through nested fields.
//
// @ Requires s != nil And 0 <= s.From.X <= s.To.X <= 1000
// @ Ensures result >= 0
func Width(s *Segment) (result int) {
	return s.To.X - s.From.X
}

// Shift writes one nested field and leaves the rest alone.
//
// @ Requires s != nil And 0 <= s.From.X <= 1000
// @ Modifies s.From
// @ Ensures s.From.X' = s.From.X + 1 And s.From.Y' = s.From.Y
func Shift(s *Segment) {
	s.From.X++
}

// ShiftKeeps relies on what Shift leaves alone.
//
// @ Requires s != nil And s.From.X = 0 And s.To.X = 7
// @ Modifies s.From
// @ Ensures result = 8
func ShiftKeeps(s *Segment) (result int) {
	Shift(s)
	return s.To.X + s.From.X
}

// Stack is a slice inside a struct.
type Stack struct {
	items []int
}

// Push appends to the stack, which may write into the capacity of its slice
// or move it to a new array.
//
// @ Requires s != nil And |s.items| < 1000
// @ Modifies s, s.items
// @ Ensures |s.items'| = |s.items| + 1 And s.items'[|s.items|] = x
// @ Ensures Forall k in [0, |s.items|) : s.items'[k] = s.items[k]
// @ Ensures fresh(s.items) Or within(s.items', s.items)
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
}

// Top reads the last element.
//
// @ Requires s != nil And |s.items| > 0
// @ Ensures result = s.items[|s.items| - 1]
func (s *Stack) Top() (result int) {
	return s.items[len(s.items)-1]
}

// PushThenTop uses both.
//
// @ Requires s != nil And |s.items| = 0
// @ Modifies s, s.items
// @ Ensures result = 9 And |s.items'| = 2 And s.items'[0] = 4
// @ Ensures fresh(s.items) Or within(s.items', s.items)
func PushThenTop(s *Stack) (result int) {
	s.Push(4)
	s.Push(9)
	return s.Top()
}

// Clear writes the elements but not the field.
//
// @ Requires s != nil
// @ Modifies s.items
// @ Ensures |s.items'| = |s.items| And Forall k in [0, |s.items|) : s.items'[k] = 0
func (s *Stack) Clear() {
	// @ Invariant Forall k in [0, i) : s.items[k] = 0
	for i := range s.items {
		s.items[i] = 0
	}
}

// Shared shows two names for one array.
//
// @ Requires |A| > 0
// @ Modifies A
// @ Ensures result = 1 And A'[0] = 1
func Shared(A []int) (result int) {
	B := A
	B[0] = 1
	return A[0]
}

// Tail returns a slice of the same array.
//
// @ Requires |A| > 1
// @ Ensures result = A[1]
func Tail(A []int) (result int) {
	B := A[1:]
	return B[0]
}

// Halves writes through two slices of one array.
//
// @ Requires |A| = 4
// @ Modifies A
// @ Ensures A'[0] = 1 And A'[2] = 2 And A'[1] = A[1] And A'[3] = A[3]
func Halves(A []int) {
	left, right := A[:2], A[2:]
	left[0] = 1
	right[0] = 2
}

// OutOfCapacity slices beyond the capacity.
//
// @ Requires |A| = 4
func OutOfCapacity(A []int) (result int) {
	B := A[1:3]
	C := B[0:4] // want `vego: slice bounds may be out of range`
	return len(C)
}

// zero clears a slice.
//
// @ Modifies A
// @ Ensures Forall k in [0, |A|) : A'[k] = 0
func zero(A []int) {
	// @ Invariant Forall k in [0, i) : A[k] = 0
	for i := range A {
		A[i] = 0
	}
}

// ZeroFront clears the first half and keeps the second. The capacity of the
// first half is cut off, since zero may write all of it.
//
// @ Requires |A| = 4 And A[3] = 7
// @ Modifies A
// @ Ensures result = 7
func ZeroFront(A []int) (result int) {
	zero(A[:2:2])
	return A[0] + A[3]
}

// ZeroFrontLoose leaves the capacity, so the call may write the second half.
//
// @ Requires |A| = 4 And A[3] = 7
// @ Modifies A
// @ Ensures result = 7
func ZeroFrontLoose(A []int) (result int) {
	zero(A[:2])
	return A[0] + A[3] // want `vego: postcondition may not hold: result = 7`
}

// copyInto copies src to dst, which must not overlap.
//
// @ Requires |dst| = |src|
// @ Modifies dst
// @ Ensures Forall k in [0, |src|) : dst'[k] = src[k]
func copyInto(dst, src []int) {
	// @ Invariant Forall k in [0, i) : dst[k] = src[k]
	for i := range src {
		dst[i] = src[i]
	}
}

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
// @ Ensures A'[0] = A[2] And A'[1] = A[3] And A'[2] = A[2]
func Disjoint(A []int) {
	copyInto(A[:2:2], A[2:])
}

// Doubled builds a new slice while reading another.
//
// @ Requires Forall k in [0, |A|) : -1000 <= A[k] <= 1000
// @ Ensures fresh(R) And |R| = |A| And Forall k in [0, |A|) : R[k] = 2 * A[k]
func Doubled(A []int) (R []int) {
	// @ Invariant |R| = i And Forall k in [0, i) : R[k] = 2 * A[k]
	for i := range A {
		R = append(R, 2*A[i])
	}
	return R
}

// AppendsToParameter may write into the caller's array without saying so.
//
// @ Requires |A| < 1000
func AppendsToParameter(A []int) (result []int) {
	return append(A, 1) // want `vego: append may write into the capacity of A, which AppendsToParameter may not modify; list it in a // @ Modifies clause`
}

// AppendsDeclared says so.
//
// @ Requires |A| < 1000
// @ Modifies A
// @ Ensures |result| = |A| + 1 And result[|A|] = 1
func AppendsDeclared(A []int) (result []int) {
	return append(A, 1)
}

// AppendAliases shows that an append may or may not share the array.
//
// @ Ensures result = 3
func AppendAliases() (result int) {
	a := make([]int, 1, 2)
	b := append(a, 5)
	b[0] = 3
	return a[0]
}

// AppendCopies appends beyond the capacity, which copies.
//
// @ Ensures result = 0
func AppendCopies() (result int) {
	a := make([]int, 1)
	b := append(a, 5)
	b[0] = 3
	return a[0]
}

// NilSlice tells a nil slice from an empty one.
//
// @ Ensures result
func NilSlice() (result bool) {
	var a []int
	b := make([]int, 0)
	return a == nil && b != nil
}

// Grid is a slice of slices.
//
// @ Requires |rows| > 1 And |rows[0]| > 0 And |rows[1]| > 0
// @ Requires rows[1][0] = 5
// @ Ensures result = 5
func Grid(rows [][]int) (result int) {
	return rows[1][0]
}

// Sum adds up the X of a slice of structs.
//
// @ Requires Forall k in [0, |ps|) : 0 <= ps[k].X <= 100
// @ Requires |ps| <= 1000
// @ Ensures 0 <= s <= 100 * |ps|
func Sum(ps []Point) (s int) {
	// @ Invariant 0 <= s <= 100 * i
	for i := range ps {
		s += ps[i].X
	}
	return s
}

// SetAll writes one field of every element.
//
// @ Modifies ps
// @ Ensures Forall k in [0, |ps|) : ps'[k].X = 1 And ps'[k].Y = ps[k].Y
func SetAll(ps []Point) {
	// @ Invariant Forall k in [0, i) : ps[k].X = 1
	// @ Invariant Forall k in [0, |ps|) : ps[k].Y = old(ps[k].Y)
	for i := range ps {
		ps[i].X = 1
	}
}

// AddressOfLocal takes the address of a variable.
//
// @ Ensures result = 0
func AddressOfLocal() (result int) {
	x := Point{}
	p := &x
	return p.X
}

// Interior points into a struct that is reached through a pointer.
//
// @ Requires s != nil
// @ Ensures result = s.From.X
func Interior(s *Segment) (result int) {
	p := &s.From
	return p.X
}

// InteriorWrite writes through a pointer into a struct, which changes the
// struct.
//
// @ Requires s != nil
// @ Modifies s
// @ Ensures result = 7 And s'.From.X = 7 And s'.From.Y = s.From.Y And s'.To.X = s.To.X
func InteriorWrite(s *Segment) (result int) {
	p := &s.From
	p.X = 7
	return s.From.X
}

// InteriorWriteWrong claims the struct kept its old value.
//
// @ Requires s != nil
// @ Modifies s
// @ Ensures s'.From.X = s.From.X
func InteriorWriteWrong(s *Segment) {
	p := &s.From
	p.X = 7
} // want `vego: postcondition may not hold: s'\.From\.X = s\.From\.X`

// InteriorUnlisted writes through a pointer into a struct it did not list.
//
// @ Requires s != nil
func InteriorUnlisted(s *Segment) {
	p := &s.From
	p.X = 7 // want `vego: p\.X is assigned, which InteriorUnlisted may not modify; list it in a // @ Modifies clause`
}

// ElementPointer points at one element of a slice of structs.
//
// @ Requires |ps| > 1 And ps[0].X = 2
// @ Modifies ps
// @ Ensures result = 7 And ps'[0].X = ps[0].X And ps'[0].Y = ps[0].Y And ps'[1].Y = ps[1].Y
func ElementPointer(ps []Point) (result int) {
	p := &ps[1]
	p.X = 5
	return ps[1].X + ps[0].X
}

// ElementPointerWrong claims the other element changed.
//
// @ Requires |ps| > 1
// @ Modifies ps
// @ Ensures ps'[0].X = 5
func ElementPointerWrong(ps []Point) {
	p := &ps[1]
	p.X = 5
} // want `vego: postcondition may not hold: ps'\[0\]\.X = 5`

// PointerIntoSlice takes a pointer that may point at an element of the
// slice it also takes, so a write through one may change the other.
//
// @ Requires p != nil And |ps| > 0 And ps[0].X = 0
// @ Modifies p
// @ Ensures result = 0
func PointerIntoSlice(p *Point, ps []Point) (result int) {
	before := ps[0].X
	p.X = 1 - before
	return ps[0].X - before // want `vego: postcondition may not hold: result = 0`
}

// PointerApartFromSlice says the pointer is not inside the slice.
//
// @ Requires p != nil And |ps| > 0 And ps[0].X = 0 And ~within(p, ps)
// @ Modifies p
// @ Ensures result = 0
func PointerApartFromSlice(p *Point, ps []Point) (result int) {
	before := ps[0].X
	p.X = 1 - before
	return ps[0].X - before
}

// ModifiesValue lists something the caller cannot see.
//
// @ Modifies p.X // want `vego: in Modifies annotation: p\.X is passed by value, so the caller cannot see a change to it`
func ModifiesValue(p Point) {
	p.X = 1
}

// PrimedValue primes a field of a value.
//
// @ Ensures result = p.X' // want `vego: in Ensures annotation: p is passed by value, so only its value on entry is visible to callers; drop the prime`
func PrimedValue(p Point) (result int) {
	return p.X
}

// LoopKeeps writes one counter in a loop and reads another afterwards.
//
// @ Requires a != nil And b != nil And a != b And b.n = 3 And 0 <= n <= 100
// @ Modifies a.n
// @ Ensures result = n + 3
func LoopKeeps(a, b *Counter, n int) (result int) {
	a.n = 0
	// @ Invariant a.n = i And 0 <= i <= n
	// @ Variant n - i
	for i := 0; i < n; i++ {
		a.n++
	}
	return a.n + b.n
}

// LoopKeepsSlices fills one slice in a loop and still knows the other.
//
// @ Requires |A| = |B| And |A| > 0 And B[0] = 4
// @ Modifies A
// @ Ensures result = 4
func LoopKeepsSlices(A, B []int) (result int) {
	// @ Invariant Forall k in [0, i) : A[k] = 0
	for i := range A {
		A[i] = 0
	}
	return A[0] + B[0]
}

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
//
// @ Ensures err = nil -> n = 2
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

// WritesForgets claims the count survives a call that may change it.
//
// @ Requires l != nil And l.count = 0
// @ Modifies l
// @ Ensures result = 0
func WritesForgets(l *Log) (result int) {
	_ = l.Write("a")
	return l.count // want `vego: postcondition may not hold: result = 0`
}

// WritesUndeclared calls a trusted method that modifies its receiver.
//
// @ Requires l != nil
func WritesUndeclared(l *Log) {
	_ = l.Write("a") // want `vego: Write may modify l, which WritesUndeclared may not modify; list it in a // @ Modifies clause`
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
// @ Ensures err = nil <-> |q.items| > 0
// @ Ensures err = nil -> x = q.items[|q.items| - 1] And |q.items'| = |q.items| - 1
func (q *Queue) Pop() (x int, err error) {
	if len(q.items) == 0 {
		return 0, errEmptyQueue
	}
	x = q.items[len(q.items)-1]
	q.items = q.items[:len(q.items)-1]
	return x, nil
}

// PopAlwaysFails never says when it succeeds.
//
// @ Requires q != nil
// @ Ensures err = nil -> x = q.items[0]
func (q *Queue) PopAlwaysFails() (x int, err error) { // want `vego: the contract of PopAlwaysFails may also be met by a function that always returns an error`
	if len(q.items) == 0 {
		return 0, errEmptyQueue
	}
	return q.items[0], nil
}

// Full succeeds when a field allows.
//
// @ Requires q != nil
// @ Ensures err = nil <-> q.max > 0
func (q *Queue) Full() (err error) {
	if q.max <= 0 {
		return errEmptyQueue
	}
	return nil
}

// Pair holds two pointers.
type Pair struct {
	left, right *Counter
}

// NilField follows a pointer read from memory without knowing it is not nil.
//
// @ Requires p != nil
func NilField(p *Pair) (result int) {
	return p.left.n // want `vego: pointer may be nil`
}

// BothFields reads through two pointers that may be the same.
//
// @ Requires p != nil And p.left != nil And p.right != nil
// @ Modifies p.left.n
// @ Ensures result = p.right.n
func BothFields(p *Pair) (result int) {
	p.left.n = 0
	return p.right.n // want `vego: postcondition may not hold: result = p\.right\.n`
}

// BothFieldsApart says that they differ.
//
// @ Requires p != nil And p.left != nil And p.right != nil And p.left != p.right
// @ Modifies p.left.n
// @ Ensures result = p.right.n
func BothFieldsApart(p *Pair) (result int) {
	p.left.n = 0
	return p.right.n
}

// SwapFields exchanges two pointers and keeps what they point to.
//
// @ Requires p != nil
// @ Modifies p
// @ Ensures p.left' = p.right And p.right' = p.left
func SwapFields(p *Pair) {
	p.left, p.right = p.right, p.left
}

// Empty has no size, so two of them need not be distinct.
type Empty struct{}

// EmptiesDiffer compares pointers that Go does not promise to differ.
//
// @ Ensures result
func EmptiesDiffer() (result bool) {
	a, b := &Empty{}, &Empty{}
	return a != b // want `vego: cannot verify EmptiesDiffer: pointers to values of size zero may or may not be equal, so comparing them is not supported`
}

// NewDiffer compares two new objects with a size.
//
// @ Ensures result
func NewDiffer() (result bool) {
	a, b := &Counter{}, new(Counter)
	return a != b && a != nil
}

// AliasInLoop writes through one slice in a loop and claims another view of
// the same array is unchanged.
//
// @ Requires |A| = 4
// @ Modifies A
// @ Ensures result = A[2]
func AliasInLoop(A []int) (result int) {
	B := A[2:]
	// @ Invariant True
	for i := range A {
		A[i] = 0
	}
	return B[0] // want `vego: postcondition may not hold: result = A\[2\]`
}

// CalleeAlias passes an alias to a function that writes it.
//
// @ Requires |A| = 4 And A[0] = 7
// @ Modifies A
// @ Ensures result = 7
func CalleeAlias(A []int) (result int) {
	B := A[:2:2]
	zero(B)
	return A[0] // want `vego: postcondition may not hold: result = 7`
}

// AppendMayAlias assumes an append copied.
//
// @ Requires |A| > 0 And |A| < 1000 And A[0] = 7
// @ Modifies A
// @ Ensures result = 7
func AppendMayAlias(A []int) (result int) {
	B := append(A, 1)
	B[0] = 3
	return A[0] // want `vego: postcondition may not hold: result = 7`
}

// BytesCapacity assumes the copy has no spare capacity.
//
// @ Requires |s| = 2
// @ Ensures result = 1
func BytesCapacity(s string) (result int) {
	b := []byte(s)
	c := append(b, 1)
	d := append(b, 2)
	return int(c[2]) - int(d[2]) + int(d[2]) // want `vego: postcondition may not hold: result = 1`
}

// Pointers is a slice of pointers.
//
// @ Requires |cs| = 2 And cs[0] != nil And cs[1] != nil And cs[0] != cs[1]
// @ Requires cs[1].n = 4
// @ Modifies cs[0]
// @ Ensures result = 5
func Pointers(cs []*Counter) (result int) {
	cs[0].n = 1
	return cs[0].n + cs[1].n
}

// RangeSeesWrites reads each element as it is when its turn comes.
//
// @ Requires |A| = 2
// @ Modifies A
// @ Ensures s = 6
func RangeSeesWrites(A []int) (s int) {
	A[0], A[1] = 1, 1
	// @ Invariant (i = 0 -> s = 0 And A[0] = 1 And A[1] = 1) And (i = 1 -> s = 1 And A[1] = 5) And (i = 2 -> s = 6)
	for i, x := range A {
		s += x
		if i == 0 {
			A[1] = 5
		}
	}
	return s
}

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
// @ Ensures result = 3
func CopyOfStruct(c *Counter) (result int) {
	saved := *c
	c.n = 2
	return saved.n + c.n
}

// ValueReceiver gets a copy of the struct, so the caller's is untouched.
//
// @ Ensures result.X = p.X And result.Y = 0
func (p Point) Moved() (result Point) {
	p.X = p.X + 0
	p.Y = 0
	return p
}

// CallsValueReceiver calls it through a pointer.
//
// @ Requires p != nil And p.Y = 3
// @ Ensures result = 3
func CallsValueReceiver(p *Point) (result int) {
	q := p.Moved()
	return q.Y + p.Y
}

// FreshParameter says a parameter is new.
//
// @ Ensures fresh(c) // want `vego: in Ensures annotation: fresh\(c\): c was passed in, so the call did not create it`
func FreshParameter(c *Counter) {}

// OneElement lists a single element of a slice of structs.
//
// @ Requires |ps| > 0
// @ Modifies ps[0]
// @ Ensures ps'[0].X = 1 And ps'[0].Y = ps[0].Y
func OneElement(ps []Point) {
	ps[0].X = 1
}

// OneElementOnly writes an element other than the one it listed.
//
// @ Requires |ps| > 1
// @ Modifies ps[0]
func OneElementOnly(ps []Point) {
	ps[1].X = 1 // want `vego: ps\[1\]\.X is assigned, which OneElementOnly may not modify: nothing its // @ Modifies clauses list is known to cover it; a clause covers what its path referred to when OneElementOnly was called`
}

// OneElementKept calls a function that changes one element and relies on
// the others being kept.
//
// @ Requires |ps| > 1
// @ Modifies ps
// @ Ensures result = 0
func OneElementKept(ps []Point) (result int) {
	before := ps[1].X
	OneElement(ps)
	return ps[1].X - before
}

// OtherPointer writes through a pointer it did not list.
//
// @ Requires |cs| = 2 And cs[0] != nil And cs[1] != nil
// @ Modifies cs[0]
func OtherPointer(cs []*Counter) {
	cs[0].n = 1
	cs[1].n = 1 // want `vego: cs\[1\]\.n is assigned, which OtherPointer may not modify: nothing its // @ Modifies clauses list is known to cover it; a clause covers what its path referred to when OtherPointer was called`
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
// @ Ensures 0 <= l.pos' <= |l.input|
// @ Ensures ok -> l.pos' = l.pos + 1 And c = l.input[l.pos]
// @ Ensures ~ok -> l.pos' = l.pos And l.pos = |l.input|
func (l *Lexer) Next() (c byte, ok bool) {
	if l.pos >= len(l.input) {
		return 0, false
	}
	c = l.input[l.pos]
	l.pos++
	return c, true
}

// CountDigits drives the lexer to the end of its input in a loop that is
// only left by break.
//
// @ Requires l != nil And l.pos = 0
// @ Modifies l.pos
// @ Ensures 0 <= n <= |l.input|
func CountDigits(l *Lexer) (n int) {
	// @ Invariant 0 <= l.pos <= |l.input| And 0 <= n <= l.pos
	// @ Variant |l.input| - l.pos
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

// Ring is a buffer that wraps around.
type Ring struct {
	buf        []int
	head, size int
}

// Put writes behind the last element.
//
// @ Requires r != nil And 0 < |r.buf| <= 1000000 And 0 <= r.head < |r.buf| And 0 <= r.size < |r.buf|
// @ Modifies r.size, r.buf
// @ Ensures r.size' = r.size + 1 And r.buf'[(r.head + r.size) % |r.buf|] = x
func (r *Ring) Put(x int) {
	r.buf[(r.head+r.size)%len(r.buf)] = x
	r.size++
}

// NewRing returns a ring nobody else has, with an array nobody else has.
//
// @ Requires n >= 0 And n <= 1000
// @ Ensures fresh(result) And fresh(result.buf) And |result.buf| = n + 1 And result.size = 0 And result.head = 0
func NewRing(n int) (result *Ring) {
	return &Ring{buf: make([]int, n+1)}
}

// UseRing may write the ring because it is new.
//
// @ Ensures result = 2
func UseRing() (result int) {
	r := NewRing(4)
	r.Put(7)
	r.Put(8)
	return r.size
}

// Config is validated field by field.
type Config struct {
	Name    string
	Retries int
	Tags    []string
}

// Valid says exactly when it succeeds, in terms of what c points to.
//
// @ Requires c != nil
// @ Ensures err = nil <-> (|c.Name| > 0 And 0 <= c.Retries <= 10)
func (c *Config) Valid() (err error) {
	if c.Name == "" {
		return errEmptyQueue
	}
	if c.Retries < 0 || c.Retries > 10 {
		return errEmptyQueue
	}
	return nil
}

// UseRingForgets claims a size the calls changed.
//
// @ Ensures result = 0
func UseRingForgets() (result int) {
	r := NewRing(4)
	r.Put(7)
	return r.size // want `vego: postcondition may not hold: result = 0`
}

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
// @ Ensures result = 0
func AliasedType(p *Counter, q *Renamed) (result int) {
	q.n = 1
	return p.n // want `vego: postcondition may not hold: result = 0`
}

// ByteIsUint8 converts between two spellings of one slice type, which shares
// the array.
//
// @ Ensures result = 0
func ByteIsUint8() (result byte) {
	a := []byte{0}
	b := []uint8(a)
	b[0] = 1
	return a[0] // want `vego: postcondition may not hold: result = 0`
}

// Partly has a field that is not modelled.
type Partly struct {
	X int
	C chan int
}

// ComparesPartly compares structs whose unmodelled fields may differ.
//
// @ Requires a.X = b.X
// @ Ensures result = True
func ComparesPartly(a, b Partly) (result bool) {
	return a == b // want `vego: cannot verify ComparesPartly: a value of type memory.Partly cannot be used here`
}

// ReadsPartly uses the modelled field of such a struct.
//
// @ Ensures result = a.X
func ReadsPartly(a Partly) (result int) {
	return a.X
}

// AppendInInit appends in the initializer of an if statement.
//
// @ Ensures result = 0
func AppendInInit() (result int) {
	s := []int{}
	if s = append(s, 1); len(s) == 0 {
		return 0
	}
	return 1 // want `vego: postcondition may not hold: result = 0`
}

// AppendInPost appends in the post statement of a loop.
//
// @ Ensures result = 3
func AppendInPost() (result int) {
	var s []int
	// @ Invariant |s| = i And 0 <= i <= 3
	// @ Variant 3 - i
	for i := 0; i < 3; s = append(s, i) {
		i++
	}
	return len(s)
}

// NamedBrk has a parameter with the name the verifier uses for the bound of
// memory.
//
// @ Ensures True
func NamedBrk(brk *Counter) (result int) {
	return brk.n // want `vego: pointer may be nil`
}

// NewFromValue uses new with a value to start from.
//
// @ Ensures result = 0
func NewFromValue() (result int) {
	p := new(Counter{n: 1})
	return p.n // want `vego: postcondition may not hold: result = 0`
}

// NewFromNil evaluates the value it starts from.
//
// @ Ensures True
func NewFromNil(p *Counter) (result *Counter) {
	return new(*p) // want `vego: pointer may be nil`
}

// MovedCapacity looks into the capacity of an array that append created.
// Nothing is known about it; in particular it does not hold what followed
// the old elements in the old array.
//
// @ Ensures result = 7
func MovedCapacity() (result byte) {
	a := []byte{0, 0, 7}
	b := append(a[:1:1], 1)
	if cap(b) > 2 {
		c := b[:cap(b)]
		return c[2] // want `vego: postcondition may not hold: result = 7`
	}
	return 7
}

// MovedElements keeps the elements that were copied.
//
// @ Ensures result = 18
func MovedElements() (result int) {
	a := []int{4, 5, 6}
	b := append(a[:2:2], 9)
	return b[0] + b[1] + b[2]
}

// Users is a slice of structs whose contract says when a search succeeds.
type Users struct {
	list []Point
}

// FindX succeeds exactly when some element has the X asked for, which is a
// condition a sample slice of structs has to meet.
//
// @ Requires u != nil
// @ Ensures err = nil <-> Exists k in [0, |u.list|) : u.list[k].X = x
func (u *Users) FindX(x int) (index int, err error) {
	// @ Invariant Forall k in [0, i) : u.list[k].X != x
	for i := range u.list {
		if u.list[i].X == x {
			return i, nil
		}
	}
	return -1, errEmptyQueue
}

// TagsShare converts a slice between struct types that differ in a tag,
// which keeps the array, so a write through one is seen through the other.
//
// @ Ensures result = 1
func TagsShare() (result int) {
	a := []struct {
		X int `a:"1"`
	}{{X: 0}}
	b := []struct {
		X int `b:"1"`
	}(a)
	b[0].X = 1
	return a[0].X
}

// TagsShareWrong claims the write is not seen.
//
// @ Ensures result = 0
func TagsShareWrong() (result int) {
	a := []struct {
		X int `a:"1"`
	}{{X: 0}}
	b := []struct {
		X int `b:"1"`
	}(a)
	b[0].X = 1
	return a[0].X // want `vego: postcondition may not hold: result = 0`
}

// Number is int under another name.
type Number = int

// SpellingsShare converts between two spellings of one struct type, which
// differ inside a field that is not modelled.
//
// @ Ensures result = 0
func SpellingsShare() (result int) {
	a := []struct {
		X int
		C chan Number
	}{{X: 0}}
	b := []struct {
		X int
		C chan int
	}(a)
	b[0].X = 1
	return a[0].X // want `vego: postcondition may not hold: result = 0`
}

// Small is a struct whose field has a narrow type.
type Small struct{ X byte }

func readySmall(a []Small) error { return nil }

// makeSmall returns a slice too long for a sample.
//
// @ Ensures |result| = 65
func makeSmall() (result []Small) {
	return make([]Small, 65)
}

// AlwaysFailsAfterReadySmall calls a function that succeeds whenever every
// field holds a value of its type, which is always.
//
// @ Ensures True
func AlwaysFailsAfterReadySmall() (result error) { // want `vego: the contract of AlwaysFailsAfterReadySmall may also be met by a function that always returns an error`
	a := makeSmall()
	_ = readySmall(a)
	return errEmptyQueue
}

// One is a struct with a single field, which is still not a single value.
type One struct{ X int }

// WholeSlice compares slices of structs as wholes, which has no meaning in
// an annotation.
//
// @ Requires |a| = 1 And a[0].X = 0
// @ Modifies a
// @ Ensures a' = a // want `vego: in Ensures annotation: a is a slice of memory.One; index it and name a field`
func WholeSlice(a []One) {
	a[0].X = 1
}

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

// StructTagsShare converts a struct that holds a slice, which keeps the
// array the slice points at.
//
// @ Requires |a.Items| > 0
// @ Modifies a.Items
// @ Ensures result = 4
func StructTagsShare(a TaggedA) (result int) {
	b := TaggedB(a)
	b.Items[0].X = 4
	return a.Items[0].X
}

// StructTagsShareWrong claims the array was copied.
//
// @ Requires |a.Items| > 0 And a.Items[0].X = 0
// @ Modifies a.Items
// @ Ensures result = 0
func StructTagsShareWrong(a TaggedA) (result int) {
	b := TaggedB(a)
	b.Items[0].X = 4
	return a.Items[0].X // want `vego: postcondition may not hold: result = 0`
}

// Blob holds bytes behind a pointer, and Named a string in each element.
type Blob struct{ B []byte }

// Named holds a string.
type Named struct{ S string }

func readyBlob(p *Blob) error    { return nil }
func readyNamed(a []Named) error { return nil }

// @ Ensures fresh(result) And |result.B| = 65
func makeBlob() (result *Blob) {
	return &Blob{B: make([]byte, 65)}
}

// @ Ensures |result| = 65
func makeNamed() (result []Named) {
	return make([]Named, 65)
}

// AlwaysFailsAfterReadyBlob calls a function that succeeds whenever the
// bytes behind its pointer are bytes.
//
// @ Ensures True
func AlwaysFailsAfterReadyBlob() (result error) { // want `vego: the contract of AlwaysFailsAfterReadyBlob may also be met by a function that always returns an error`
	p := makeBlob()
	_ = readyBlob(p)
	return errEmptyQueue
}

// AlwaysFailsAfterReadyNamed calls one that succeeds whenever the bytes of
// the strings in its elements are bytes.
//
// @ Ensures True
func AlwaysFailsAfterReadyNamed() (result error) { // want `vego: the contract of AlwaysFailsAfterReadyNamed may also be met by a function that always returns an error`
	a := makeNamed()
	_ = readyNamed(a)
	return errEmptyQueue
}

func readyRows(a [][]byte) error { return nil }

// @ Ensures |result| = 65
func makeRows() (result [][]byte) {
	return make([][]byte, 65)
}

// AlwaysFailsAfterReadyRows calls a function that succeeds whenever the
// slices in its slice have lengths that are not negative.
//
// @ Ensures True
func AlwaysFailsAfterReadyRows() (result error) { // want `vego: the contract of AlwaysFailsAfterReadyRows may also be met by a function that always returns an error`
	a := makeRows()
	_ = readyRows(a)
	return errEmptyQueue
}
