// Package ptrstates holds the states of what a pointer points to (S0b of
// F34): one state for a pointer and for every interface value that holds
// it, changed by a call on the pointer as by one through any of them.
package ptrstates

import (
	"io"
	"os"
	"ptrlib"
)

// The four shapes the reviewer found at the base, each of which verified
// and is false at run time (run_test.go).

// @Requires 0 < |name| <= 1000
// @Ensures err = nil -> c != nil And ~closed(c)
func FileClosedThenReturned(name string) (c io.Closer, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, err
	}
	var cc io.Closer = f
	f.Close()
	return cc, nil // want `postcondition may not hold: err = nil -> c != nil And ~closed\(c\)`
}

// @Requires 0 < |name| <= 1000
// @Ensures err = nil -> c != nil And ~closed(c)
func ClosedBeforeConversion(name string) (c io.Closer, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, err
	}
	f.Close()
	var cc io.Closer = f
	return cc, nil // want `postcondition may not hold: err = nil -> c != nil And ~closed\(c\)`
}

// @Requires 0 < |name| <= 1000
// @Ensures err = nil -> c != nil And ~closed(c)
func TwoConversions(name string) (c io.Closer, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, err
	}
	var c1 io.Closer = f
	c1.Close()
	var c2 io.Closer = f
	return c2, nil // want `postcondition may not hold: err = nil -> c != nil And ~closed\(c\)`
}

// P is a closer of the project, whose state closed is ghost.
type P struct{ n int }

// @Requires p != nil
// @Modifies p
// @Ensures err = nil
func (p *P) Close() (err error) {
	if p.n < 100 {
		p.n++
	}
	return nil
}

// @Ensures result != nil And ~closed(result)
func ClosedThenReturned() (result io.Closer) {
	p := &P{}
	var c io.Closer = p
	p.Close()
	return c // want `postcondition may not hold: ~closed\(result\)`
}

// The fifth shape: a file a caller passes may be closed.

// @Requires f != nil
// @Modifies f
// @Ensures True
func FromParam(f *os.File) {
	var c io.Closer = f
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// What a contract says of the file lets it verify.

// @Requires f != nil And ~closed(f)
// @Modifies f
// @Ensures closed(f')
func FromParamOpen(f *os.File) {
	var c io.Closer = f
	c.Close()
}

// Honest forms keep verifying: a file that os.Open returned is not closed,
// one Close through the interface value or on the file closes it, and two
// conversions of one file share its state.

// @Requires 0 < |name| <= 1000
// @Ensures True
func OpenThenClose(name string) (err error) {
	f, err := os.Open(name)
	if err != nil {
		return err
	}
	var c io.Closer = f
	defer c.Close()
	return nil
}

// @Requires 0 < |name| <= 1000
// @Ensures err = nil -> c != nil And ~closed(c)
func OpenAndConvert(name string) (c io.Closer, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, err
	}
	var c1 io.Closer = f
	var c2 io.Closer = f
	_ = c1
	return c2, nil
}

// @Requires 0 < |name| <= 1000
// @Ensures True
func CloseOnce(name string) {
	f, err := os.Open(name)
	if err != nil {
		return
	}
	var c io.Closer = f
	f.Close()
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// @Ensures result != nil And closed(result)
func ClosedProject() (result io.Closer) {
	p := &P{}
	var c io.Closer = p
	c.Close()
	var d io.Closer = p
	return d
}

// Two files are two objects.
//
// @Requires f != nil And g != nil And f != g And ~closed(f) And ~closed(g)
// @Modifies f
// @Ensures closed(f') And ~closed(g')
func OneOfTwo(f, g *os.File) {
	var c io.Closer = f
	c.Close()
}

// The states of a library's connection are about the file it holds, which
// nothing here sees, so a literal of it has unknown states (F10).

// @Requires f != nil
// @Ensures True
func TwoConns(f *os.File) {
	a := &ptrlib.Conn{FD: f}
	b := &ptrlib.Conn{FD: f}
	var ca io.Closer = a
	var cb io.Closer = b
	ca.Close() // want `precondition of ca.Close may not hold: ~closed\(c\)`
	cb.Close() // want `precondition of cb.Close may not hold: ~closed\(c\)`
}

// A copy of a struct whose states trusted methods change would share them
// (F10).

// @Requires 0 < |name| <= 1000
// @Ensures err = nil -> c != nil And ~closed(c)
func CopyAfterClose(name string) (c io.Closer, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, err
	}
	f.Close()
	g := *f // want `cannot verify CopyAfterClose: Go copies a value of type os.File, here`
	h := &g
	var cc io.Closer = h
	return cc, nil
}

// @Requires f != nil
// @Ensures True
func StoreCopy(f *os.File) {
	p := new(os.File)
	*p = *f // want `cannot verify StoreCopy: Go copies a value of type os.File, here`
}

// Pointer states in a formula name states of an interface the type
// implements, and nothing else.

// @Requires f != nil And ~shut(f) // want `unknown predicate shut`
// @Ensures True
func NoSuchState(f *os.File) {
}

// A struct and its first field lie at one address, and both have states of
// their own, so nothing tells them apart.

// Outer holds a P first.
type Outer struct {
	in P
	m  int
}

// @Requires o != nil
// @Modifies o
// @Ensures err = nil
func (o *Outer) Close() (err error) {
	if o.m < 100 {
		o.m++
	}
	return nil
}

// @Ensures True
func FirstField() {
	o := &Outer{}
	var c io.Closer = o // want `cannot verify FirstField: converting a \*Outer to io.Closer is not supported: its first field holds a P, whose states are its own and lie at the same address`
	c.Close()
}

// A pointer and an interface value of which the contract lists one are
// assumed to have states of their own, and every verified caller proves it.

// @Requires c != nil And f != nil And ~closed(c) And ~closed(f)
// @Modifies f
// @Ensures ~closed(c')
func CloseFileKeepCloser(c io.Closer, f *os.File) {
	f.Close()
}

// @Requires 0 < |name| <= 1000
// @Ensures True
func PassesSame(name string) {
	f, err := os.Open(name)
	if err != nil {
		return
	}
	var c io.Closer = f
	CloseFileKeepCloser(c, f) // want `the interface value and the pointer passed to CloseFileKeepCloser as c and f may share their states: the interface value may hold the pointer`
}

// @Requires 0 < |name| <= 1000
// @Ensures True
func PassesTwo(name string) {
	f, err := os.Open(name)
	if err != nil {
		return
	}
	g, err := os.Open(name)
	if err != nil {
		return
	}
	var c io.Closer = g
	CloseFileKeepCloser(c, f)
}

// A loop forgets the states of what a call in it may close.

// @Requires 0 < |name| <= 1000 And 0 < n <= 3
// @Ensures err = nil -> c != nil And ~closed(c)
func LoopClose(name string, n int) (c io.Closer, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, err
	}
	var cc io.Closer = f
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		f.Close()
	}
	return cc, nil // want `postcondition may not hold: err = nil -> c != nil And ~closed\(c\)`
}

// Two names of one file have one state.

// @Requires f != nil And f = g And ~closed(f)
// @Modifies f
// @Ensures ~closed(g')
func AliasClosed(f, g *os.File) {
	var c io.Closer = f
	c.Close()
} // want `postcondition may not hold: ~closed\(g'\)`

// A pointer whose method that changes its states does not list its receiver
// has no states: a call of it would not be known to change them (F12 of
// the review of S0b).

// Q is a closer of the project whose Close lists nothing.
type Q struct{ n int }

// @Requires q != nil
// @Ensures err = nil
func (q *Q) Close() (err error) { return nil }

// @Ensures result != nil And ~closed(result) // want `closed\(result\): the states of what result points to are not kept: \(\*Q\).Close changes its states, and its contract does not list its receiver q in Modifies`
func ClosedGhost() (result *Q) {
	q := &Q{}
	q.Close()
	return q
}

// @Requires c != nil And ~closed(c) // want `closed\(c\): the states of what c points to are not kept: \(\*ptrlib.Quiet\).Close changes its states, and its contract does not list its receiver`
// @Ensures ~closed(c')
func StillOpen(c *ptrlib.Quiet) (err error) {
	return c.Close()
}

// @Ensures True
func ConvertQ() {
	var c io.Closer = &Q{} // want `cannot verify ConvertQ: converting a \*Q to io.Closer is not supported: \(\*Q\).Close changes its states, and its contract does not list its receiver q in Modifies`
	c.Close()
}

// A range over files by value copies each, and so does a struct that holds
// one.

// @Requires |fs| <= 10
// @Ensures True
func RangeCopies(fs []os.File) {
	for _, f := range fs { // want `cannot verify RangeCopies: Go copies a value of type os.File, here \(the range over fs\)`
		_ = f
	}
}

// Holder holds a file by value.
type Holder struct {
	n int
	F os.File
}

// @Requires h != nil
// @Ensures True
func HolderCopy(h *Holder) {
	g := *h // want `cannot verify HolderCopy: Go copies a value of type Holder, which holds an os.File, here \(\*h\)`
	_ = g
}

// Two files that two calls returned, each converted and closed through its
// interface value, keep their states apart (O1 of the checkpoint of S0b):
// the key of an object that exists exists too, so a call does not create
// it, and no footprint that the call grows holds it.

// @Requires 0 < |n1| <= 100 And 0 < |n2| <= 100
// @Ensures True
func TwoFiles(n1, n2 string) {
	f1, err := os.Open(n1)
	if err != nil {
		return
	}
	var c1 io.Closer = f1
	f2, err := os.Create(n2)
	if err != nil {
		c1.Close()
		return
	}
	var c2 io.Closer = f2
	c1.Close()
	c2.Close()
}

// @Requires 0 < |n1| <= 100 And 0 < |n2| <= 100
// @Ensures True
func TwoOpened(n1, n2 string) {
	f1, err := os.Open(n1)
	if err != nil {
		return
	}
	f2, err := os.Open(n2)
	if err != nil {
		return
	}
	var c1 io.Closer = f1
	var c2 io.Closer = f2
	c2.Close()
	c1.Close()
}

// @Requires 0 < |n1| <= 100 And 0 < |n2| <= 100
// @Ensures True
func OneConverted(n1, n2 string) {
	f1, err := os.Open(n1)
	if err != nil {
		return
	}
	f2, err := os.Open(n2)
	if err != nil {
		return
	}
	var c1 io.Closer = f1
	c1.Close()
	// @Assert ~closed(f2)
	f2.Close()
}

// NewP makes a closer of the project.
//
// @Ensures result != nil And fresh(result) And ~closed(result)
func NewP() (result *P) {
	return &P{}
}

// @Ensures True
func TwoConstructed() {
	p1 := NewP()
	p2 := NewP()
	var c1 io.Closer = p1
	var c2 io.Closer = p2
	c1.Close()
	c2.Close()
}

// newTrustedP is trusted: its entry says the closer is new and not closed.
func newTrustedP() (result *P) { return &P{} }

// @Ensures True
func TwoTrusted() {
	p1 := newTrustedP()
	p2 := newTrustedP()
	var c1 io.Closer = p1
	var c2 io.Closer = p2
	c1.Close()
	c2.Close()
}
