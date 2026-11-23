package frames

import "io"

// GR: a call that writes no footprint grows the row of a value that
// existed before it only by a store into a cell of that row (frames.go).

// Pile owns the array of its slice.
//
// @Owns items
type Pile struct {
	items []int
}

// Push appends x, which may move the array.
//
// @Requires p != nil And |p.items| < 1000000
// @Modifies p
// @Ensures |p.items'| = |p.items| + 1 And p.items'[|p.items|] = x
func (p *Pile) Push(x int) {
	p.items = append(p.items, x)
}

// PushThenWrite pushes and then answers: what the push made is no part of
// what w writes, since the push wrote nothing w's row held.
//
// @Requires p != nil And w != nil And |p.items| = 0
// @Modifies p, w
// @Ensures |p.items'| = 1 And p.items'[0] = 5
func PushThenWrite(p *Pile, w io.Writer, b []byte) {
	p.Push(5)
	w.Write(b)
}

// WriteThenPush answers and then pushes, which verifies at the base too.
//
// @Requires p != nil And w != nil And |p.items| = 0
// @Modifies p, w
// @Ensures |p.items'| = 1 And p.items'[0] = 5
func WriteThenPush(p *Pile, w io.Writer, b []byte) {
	w.Write(b)
	p.Push(5)
}

// Index owns a map that Put makes when it has none.
//
// @Owns m
type Index struct {
	m map[int]int
}

// Put sets a key, making the map first if there is none.
//
// @Requires ix != nil
// @Modifies ix
// @Ensures has(ix.m', k) And ix.m'[k] = x
func (ix *Index) Put(k, x int) {
	if ix.m == nil {
		ix.m = map[int]int{}
	}
	ix.m[k] = x
}

// PutThenWrite puts a key into a map the call may have made, then answers.
//
// @Requires ix != nil And w != nil
// @Modifies ix, w
// @Ensures ix.m'[3] = 7
func PutThenWrite(ix *Index, w io.Writer, b []byte) {
	ix.Put(3, 7)
	w.Write(b)
}

// Cell is what a Holder owns through a pointer.
type Cell struct{ n int }

// Holder owns a cell, which Reset replaces.
//
// @Owns c
type Holder struct {
	c *Cell
}

// Reset gives the holder a new cell.
//
// @Requires h != nil
// @Modifies h
// @Ensures h.c' != nil And h.c'.n = x
func (h *Holder) Reset(x int) {
	h.c = &Cell{n: x}
}

// ResetThenWrite replaces the cell, then answers.
//
// @Requires h != nil And w != nil
// @Modifies h, w
// @Ensures h.c'.n = 4
func ResetThenWrite(h *Holder, w io.Writer, b []byte) {
	h.Reset(4)
	w.Write(b)
}

// PushTo pushes and writes w: it is handed the writer, so it writes its
// footprint, and what it made may be what w writes.
//
// @Requires p != nil And w != nil And |p.items| < 1000000
// @Modifies p, w
// @Ensures |p.items'| = |p.items| + 1
func (p *Pile) PushTo(w io.Writer, x int) {
	w.Write(nil)
	p.items = append(p.items, x)
}

// HandedTheWriter pushes through a call that writes w, then answers.
//
// @Requires p != nil And w != nil And |p.items| = 0
// @Modifies p, w
// @Ensures |p.items'| = 1 And p.items'[0] = 5
func HandedTheWriter(p *Pile, w io.Writer, b []byte) {
	p.PushTo(w, 5)
	w.Write(b)
} // want `vego: postcondition may not hold: p\.items'\[0\] = 5`

// Sink is written behind its receiver.
type Sink interface {
	// @Receiver r
	// @Modifies r
	// @Ensures True
	Put(x int)
}

// Put writes the first element of what the pile owns.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func (p *Pile) Put(x int) {
	if len(p.items) > 0 {
		p.items[0] = x
	}
}

// IntoTheRow pushes onto a pile converted to a Sink: the push stores into
// a cell of the sink's row, so the new array may be what Put writes, and
// it is.
//
// @Ensures r
func IntoTheRow() (r bool) {
	p := &Pile{}
	var s Sink = p
	p.Push(5)
	items := p.items
	s.Put(9)
	return items[0] == 5 // want `vego: postcondition may not hold: r`
}

// refill gives the second pile of a slice of piles new memory: the
// target is the range of the slice, whose elements own memory, so GR
// does not apply (F13 of the review).
//
// @Requires |ps| > 1
// @Modifies ps
// @Ensures |ps[1].items'| = 1 And ps[1].items'[0] = 5
func refill(ps []Pile) { ps[1].items = []int{5} }

// Elements refills a pile in a slice of piles, one of which is a Sink.
//
// @Ensures r
func Elements() (r bool) {
	ps := make([]Pile, 4)
	var s Sink = &ps[1]
	refill(ps)
	items := ps[1].items
	s.Put(9)
	return items[0] == 5 // want `vego: postcondition may not hold: r`
}

// Through holds a pile it does not own.
type Through struct {
	p *Pile
}

// refillThrough stores new memory into the pile a Through points to.
//
// @Requires h != nil And h.p != nil
// @Modifies h.p
// @Ensures |h.p.items'| = 1 And h.p.items'[0] = 5
func refillThrough(h *Through) { h.p.items = []int{5} }

// HandedSomethingElse converts a pile and hands a callee something else
// that reaches it: the callee's target is the pile's struct, which lies in
// the sink's row, so GR does not apply (F13 of the review).
//
// @Ensures r
func HandedSomethingElse() (r bool) {
	p := &Pile{}
	var s Sink = p
	h := &Through{p: p}
	refillThrough(h)
	items := p.items
	s.Put(9)
	return items[0] == 5 // want `vego: postcondition may not hold: r`
}

// PushInLoopThenWrite pushes in a loop and then answers: GR does not
// change the growth layer of a loop's head, so what the loop made may lie
// in w's row and the fact about it is not kept. Not built.
//
// @Requires p != nil And w != nil And |p.items| = 0 And n = 1
// @Modifies p, w
// @Ensures |p.items'| = 1 And p.items'[0] = 5
func PushInLoopThenWrite(p *Pile, w io.Writer, b []byte, n int) {
	// @Invariant |p.items| = k And k <= n And (k > 0 -> p.items[0] = 5)
	// @Variant n - k
	for k := 0; k < n; k++ {
		p.Push(5)
	}
	w.Write(b)
} // want `vego: postcondition may not hold: p\.items'\[0\] = 5`
