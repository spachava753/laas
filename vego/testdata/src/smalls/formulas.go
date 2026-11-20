package smalls

import "errors"

// Character literals stand for the number of their character.

// @Ensures r <-> (|s| > 0 And s[0] = '/')
func IsAbs(s string) (r bool) {
	return len(s) > 0 && s[0] == '/'
}

// @Ensures r <-> (|s| > 0 And s[0] = '\\')
func IsAbsWrong(s string) (r bool) {
	return len(s) > 0 && s[0] == '/' // want `postcondition may not hold: r <-> \(\|s\| > 0 And s\[0\] = '\\\\'\)`
}

// gofmt turns two quotes in a row in a doc comment into a closing quote
// mark, so a quote is written '\x27' there.
//
// @Ensures r <-> (|s| > 0 And (s[0] = '\n' Or s[0] = '\t' Or s[0] = '\x20' Or s[0] = '\x27'))
func StartsBlank(s string) (r bool) {
	if len(s) > 0 && s[0] == '\'' {
		// @Assert s[0] = '\''
		return true
	}
	return len(s) > 0 && (s[0] == '\n' || s[0] == '\t' || s[0] == ' ')
}

// @Ensures r <-> s = "”"
func Mangled(s string) (r bool) {
	return s == "”"
}

// @Ensures r = ’a’ // want `syntax error in Ensures annotation: unexpected character '’'`
func CurlyQuotes() (r int) {
	return 'a'
}

// cap in a formula is the capacity of a slice.

// @Requires |A| < cap(A)
// @Modifies A
// @Ensures |r| = |A| + 1 And cap(r) = cap(A) And r[|A|] = x
func Push(A []int, x int) (r []int) {
	return append(A, x)
}

// @Requires |A| < cap(A)
// @Modifies A
// @Ensures cap(r) = cap(A) + 1
func PushWrong(A []int, x int) (r []int) {
	return append(A, x) // want `postcondition may not hold: cap\(r\) = cap\(A\) \+ 1`
}

// @Requires n >= 0 And n <= 1000
// @Ensures |r| = 0 And cap(r) = n And r != nil And fresh(r)
func Reserve(n int) (r []int) {
	return make([]int, 0, n)
}

// A slice compares with nil as in code.

// @Ensures (A = nil -> n = -1) And (A != nil -> n = |A|)
func Measure(A []int) (n int) {
	if A == nil {
		return -1
	}
	return len(A)
}

// Point is a struct, so a slice of points has no sequence of its own in a
// formula; it still compares with nil.
type Point struct{ X, Y int }

// @Ensures ok <-> ps != nil
func HasArray(ps []Point) (ok bool) {
	return ps != nil
}

// @Ensures r != nil
func EmptyOf(A []int) (r []int) {
	return A[:0] // want `postcondition may not hold: r != nil`
}

// @Ensures r = nil <-> old(A) = nil
func Same(A []int) (r []int) {
	return A
}

// @Ensures |s| = 0 -> s = nil // want `in Ensures annotation: s is a string, which is never nil; compare \|s\| with 0`
func NeverNil(s string) (n int) {
	return len(s)
}

// A contract that says when a function succeeds by nil or by capacity
// is one some input meets.

// @Ensures err = nil <-> A != nil
func Present(A []int) (err error) {
	if A == nil {
		return errors.New("no array")
	}
	return nil
}

// @Ensures err = nil <-> cap(A) > |A|
func Room(A []int) (err error) {
	if cap(A) == len(A) {
		return errors.New("full")
	}
	return nil
}

// apart says that two slices share no memory.

type Halves struct{ a, b []int }

// @Requires h != nil And |h.a| > 0 And |h.b| > 0 And apart(h.a, h.b)
// @Modifies h.a
// @Ensures h.b'[0] = h.b[0] And h.a'[0] = 1
func SetFirst(h *Halves) {
	h.a[0] = 1
}

// @Requires h != nil And |h.a| > 0 And |h.b| > 0
// @Modifies h.a
// @Ensures h.b'[0] = h.b[0]
func SetFirstWrong(h *Halves) {
	h.a[0] = 1
} // want `postcondition may not hold: h.b'\[0\] = h.b\[0\]`

// @Requires |A| <= 1000
// @Ensures apart(r, A) And |r| = |A|
func Copy(A []int) (r []int) {
	// @Invariant |r| = i
	for i := range A {
		r = append(r, A[i])
	}
	return r
}

type Names struct {
	n []int
	s []string
}

// @Requires p != nil And apart(p.n, p.s) // want `in Requires annotation: apart\(p.n, p.s\): a slice of int and a slice of string never share memory, so there is nothing to state`
// @Ensures True
func Mixed(p *Names) {
}

// @Requires p != nil And apart(p, p.n) // want `in Requires annotation: apart\(p, ...\): p is not a slice; apart says that two slices share no memory`
// @Ensures True
func NotSlices(p *Names) {
}

// & in a formula is the address of a struct reached through memory.

type Element struct {
	next *Element
	list *List
	n    int
}

type List struct {
	root Element
	tail Element
}

// @Requires e != nil
// @Ensures result = nil <-> (e.list = nil Or e.next = nil Or e.next = &e.list.root)
// @Ensures result != nil -> result = e.next
func (e *Element) Next() (result *Element) {
	if p := e.next; e.list != nil && p != &e.list.root {
		return p
	}
	return nil
}

// @Requires l != nil
// @Ensures p = &l.tail
func Tail(l *List) (p *Element) {
	return &l.root // want `postcondition may not hold: p = &l.tail`
}

// @Requires 0 <= i < |s|
// @Ensures p = &s[i]
func At(s []Element, i int) (p *Element) {
	return &s[i]
}

// @Requires 0 <= i < |s| - 1
// @Ensures p = &s[i]
func AtWrong(s []Element, i int) (p *Element) {
	return &s[i+1] // want `postcondition may not hold: p = &s\[i\]`
}

// The address of a field of a nil pointer is nil in a formula, where Go
// would panic.

// @Requires e != nil And e.list = nil
// @Ensures &e.list.root = nil And &e.list.tail = nil
func Detached(e *Element) {
}

// A path read on return: the prime may stand on any of its parts.

// @Requires e != nil And l != nil
// @Modifies e
// @Ensures &e.list'.root = &l.root And &e'.list.tail = &l.tail
func Attach(e *Element, l *List) {
	e.list = l
}

// @Requires e != nil
// @Ensures &e.n = nil // want `in Ensures annotation: &e.n: e.n has type int, and & gives only pointers to structs`
func NotAStruct(e *Element) {
}

// @Requires l != nil
// @Ensures &l = nil // want `in Ensures annotation: & takes a field or an element reached from a variable through a pointer or a slice, as in &e.list.root or &s\[i\]`
func NotAPath(l *List) {
}

type Holder struct{ in List }

// @Ensures &h.in = &h.in // want `in Ensures annotation: &h.in: h.in is not reached through a pointer or an element of a slice, so it has no address a formula can name`
func ByValue(h Holder) {
}

type Empty struct{}

type WithEmpty struct {
	e Empty
	n int
}

// @Requires w != nil
// @Ensures &w.e = &w.e // want `in Ensures annotation: pointers to values of size zero may or may not be equal, so they can only be compared with nil`
func Sizeless(w *WithEmpty) {
}

// @Ensures err = nil <-> A = nil
func Absent(A []int) (err error) {
	if A != nil {
		return errors.New("an array")
	}
	return nil
}

// @Requires e != nil
// @Ensures result = nil <-> (e.list = nil Or e.next = &e.list.root)
func (e *Element) NextWrong() (result *Element) {
	if p := e.next; e.list != nil && p != &e.list.root {
		return p // want `postcondition may not hold: result = nil <-> \(e.list = nil Or e.next = &e.list.root\)`
	}
	return nil
}

// @Requires |A| > 0
// @Ensures apart(r, A)
func Alias(A []int) (r []int) {
	return A[1:] // want `postcondition may not hold: apart\(r, A\)`
}

type Stack struct{ items []int }

// @Requires s != nil And |s.items| < cap(s.items)
// @Modifies s, s.items
// @Ensures cap(s.items') = cap(s.items) And |s.items'| = |s.items| + 1
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
}

// @Requires s != nil And |s.items| < cap(s.items)
// @Modifies s, s.items
// @Ensures cap(s.items') = cap(s.items) + 1
func (s *Stack) PushWrong(x int) {
	s.items = append(s.items, x)
} // want `postcondition may not hold: cap\(s.items'\) = cap\(s.items\) \+ 1`
