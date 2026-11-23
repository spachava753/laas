// Package footprints holds programs that write behind the receiver of an
// interface value, through interfaces declared in source without states.
package footprints

import (
	"errors"
	"io"
)

// Sink takes bytes, and keeps what it is given in memory of its own.
type Sink interface {
	// Put adds p.
	//
	// @Receiver s
	// @Requires |p| <= 100
	// @Modifies s
	// @Ensures 0 <= n <= |p|
	Put(p []byte) (n int)
}

// Peeker hands out a pair it holds.
type Peeker interface {
	// @Ensures p != nil
	Peek() (p *Pair)
}

// Pair is two numbers.
type Pair struct{ A, B int }

// Keeps writes through s, and q, which the caller passed beside it, is not
// part of what s writes.
//
// @Requires s != nil And q != nil And |p| <= 100
// @Modifies s
// @Ensures q.A' = q.A
func Keeps(s Sink, q *Pair, p []byte) {
	s.Put(p)
}

// KeepsDeep keeps what a parameter reaches through a pointer field.
//
// @Requires s != nil And h != nil And h.P != nil
// @Modifies s
// @Ensures h.P.A' = h.P.A
func KeepsDeep(s Sink, h *Holder) {
	s.Put(nil)
}

// Holder holds a pair and a sink.
type Holder struct {
	P *Pair
	S Sink
}

// Lines writes every line, whose bounds survive the writes.
//
// @Requires s != nil And (Forall k in [0, |lines|) : |lines[k]| <= 100)
// @Modifies s
// @Ensures True
func Lines(s Sink, lines [][]byte) {
	for i := range lines {
		s.Put(lines[i])
	}
}

// OwnNew keeps memory it made itself.
//
// @Requires s != nil
// @Modifies s
// @Ensures r = 7
func OwnNew(s Sink) (r int) {
	q := &Pair{A: 7}
	s.Put(nil)
	return q.A
}

// InLoop keeps q across a loop that writes through s.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures q.A' = q.A
func InLoop(s Sink, q *Pair) {
	// @Invariant 0 <= i <= 3
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		s.Put(nil)
	}
}

// OnBranch writes through s on one branch only.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures q.A' = q.A
func OnBranch(s Sink, q *Pair, c bool) {
	if c {
		s.Put(nil)
	}
}

// InLiteral writes through s in a literal called in place.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures q.A' = q.A
func InLiteral(s Sink, q *Pair, c bool) {
	func() {
		if c {
			s.Put(nil)
		}
	}()
}

// OverMap writes through s while it ranges over a map it was given.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func OverMap(s Sink, m map[int]int) {
	for range m {
		s.Put(nil)
	}
}

// Passes hands s on with a number, which refers to no memory.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Passes(s Sink) {
	PutN(s, 3)
}

// @Requires s != nil
// @Modifies s
// @Ensures True
func PutN(s Sink, n int) {
	if n > 0 {
		s.Put(nil)
	}
}

// Unlisted writes through s without listing it.
//
// @Requires s != nil
// @Ensures True
func Unlisted(s Sink) {
	s.Put(nil) // want `s.Put may modify the footprint of s, which Unlisted may not modify; list it in a // @Modifies clause`
}

// Peeked does not keep a pair it got from a call, which may lie in what s
// writes.
//
// @Requires s != nil And g != nil
// @Modifies s
// @Ensures r = 1
func Peeked(s Sink, g Peeker) (r int) {
	p := g.Peek()
	if p.A != 1 {
		return 1
	}
	s.Put(nil)
	return p.A // want `postcondition may not hold: r = 1`
}

// NotNeeded lists s and never writes it.
//
// @Requires s != nil
// @Modifies s // want `Modifies lists s, but NotNeeded never needs to modify it`
// @Ensures True
func NotNeeded(s Sink) {
}

// StateLost does not keep the state of another interface value, which may
// lie in what s writes.
//
// @Requires s != nil And c != nil And ~closed(c)
// @Modifies s, c
// @Ensures True
func StateLost(s Sink, c io.Closer) {
	s.Put(nil)
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// SinkCloser has a state from io.Closer and a method that writes behind
// its receiver.
type SinkCloser interface {
	Sink
	io.Closer
}

// @Requires s != nil
// @Modifies s
// @Ensures True
func ThroughStates(s SinkCloser) {
	s.Put(nil)
}

// PutThenClose writes through s and then closes it: Put is declared on
// Sink, which has no states, so it keeps closed of the value it writes.
//
// @Requires s != nil And ~closed(s)
// @Modifies s
// @Ensures closed(s')
func PutThenClose(s SinkCloser) {
	s.Put(nil)
	s.Close()
}

// PutThenCloseOther writes through one value and closes another, whose
// state may lie in what the first writes.
//
// @Requires s != nil And c != nil And ~closed(c)
// @Modifies s, c
// @Ensures True
func PutThenCloseOther(s SinkCloser, c SinkCloser) {
	s.Put(nil)
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// CallsKeeps passes a parameter beside s, which its own Modifies lists.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures True
func CallsKeeps(s Sink, q *Pair) {
	Keeps(s, q, nil)
}

// Maker hands out new pairs that it may keep in its own memory.
type Maker interface {
	// @Receiver m
	// @Modifies m
	// @Ensures p != nil And fresh(p)
	New() (p *Pair)

	// @Receiver m
	// @Modifies m
	// @Ensures True
	Touch()
}

// MadeKept relies on a pair that m made staying as it was across a later
// call of m, which may write what it made.
//
// @Requires m != nil
// @Modifies m
// @Ensures r = 5
func MadeKept(m Maker) (r int) {
	p := m.New()
	p.A = 5
	m.Touch()
	return p.A // want `postcondition may not hold: r = 5`
}

// NilBeside may be given a nil q.
//
// @Requires s != nil
// @Modifies s
// @Ensures q != nil
func NilBeside(s Sink, q *Pair) {
	s.Put(nil)
} // want `postcondition may not hold: q != nil`

// GuardedPut writes through s on the right of &&.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures q.A' = q.A
func GuardedPut(s Sink, q *Pair, c bool) (ok bool) {
	return c && s.Put(nil) == 0
}

// Shelf hands out a map it holds.
type Shelf interface {
	// @Ensures m != nil
	Items() (m map[int]int)
}

// GuardedPeek writes through s on the right of && and keeps a pair that
// may lie in what s writes.
//
// @Requires s != nil And g != nil
// @Modifies s
// @Ensures r = 1
func GuardedPeek(s Sink, g Peeker, c bool) (r int) {
	p := g.Peek()
	if p.A != 1 {
		return 1
	}
	if c && s.Put(nil) == 0 {
		return p.A // want `postcondition may not hold: r = 1`
	}
	return p.A
}

// LoopPeek writes through s in a loop and keeps a pair that may lie in
// what s writes.
//
// @Requires s != nil And g != nil
// @Modifies s
// @Ensures r = 1
func LoopPeek(s Sink, g Peeker) (r int) {
	p := g.Peek()
	if p.A != 1 {
		return 1
	}
	// @Invariant 0 <= i <= 3
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		s.Put(nil)
	}
	return p.A // want `postcondition may not hold: r = 1`
}

// LiteralPeek writes through s in a literal called in place.
//
// @Requires s != nil And g != nil
// @Modifies s
// @Ensures r = 1
func LiteralPeek(s Sink, g Peeker, c bool) (r int) {
	p := g.Peek()
	if p.A != 1 {
		return 1
	}
	func() {
		if c {
			s.Put(nil)
		}
	}()
	return p.A // want `postcondition may not hold: r = 1`
}

// RangedPeek writes through s while it ranges over a map that may lie in
// what s writes.
//
// @Requires s != nil And h != nil
// @Modifies s
// @Ensures True
func RangedPeek(s Sink, h Shelf) {
	m := h.Items()
	for range m {
		s.Put(nil) // want `s.Put may modify m while the loop at footprints.go:\d+:\d+ ranges over it, since the map may lie in the footprint of what it is called on`
	}
}

// NilMap may be given the nil map, and reads it after a write through s.
//
// @Requires s != nil
// @Modifies s
// @Ensures m != nil
func NilMap(s Sink, m map[int]int) (r int) {
	s.Put(nil)
	return m[1] // want `postcondition may not hold: m != nil`
}

// Cell holds a pair.
type Cell struct{ P *Pair }

// RepointField points a field of a parameter at a pair that may lie in what
// s writes, and reads it after a write through s.
//
// @Requires s != nil And g != nil And c != nil
// @Modifies s, c
// @Ensures r = 1
func RepointField(s Sink, g Peeker, c *Cell) (r int) {
	p := g.Peek()
	if p.A != 1 {
		return 1
	}
	c.P = p
	q := c.P
	s.Put(nil)
	return q.A // want `postcondition may not hold: r = 1`
}

// RepointElem does the same through an element of a slice.
//
// @Requires s != nil And g != nil And |ps| > 0
// @Modifies s, ps
// @Ensures r = 1
func RepointElem(s Sink, g Peeker, ps []*Pair) (r int) {
	p := g.Peek()
	if p.A != 1 {
		return 1
	}
	ps[0] = p
	s.Put(nil)
	return ps[0].A // want `postcondition may not hold: r = 1`
}

// RepointMap does the same through an entry of a map.
//
// @Requires s != nil And g != nil And m != nil
// @Modifies s, m
// @Ensures r = 1
func RepointMap(s Sink, g Peeker, m map[int]*Pair) (r int) {
	p := g.Peek()
	if p.A != 1 {
		return 1
	}
	m[0] = p
	s.Put(nil)
	q := m[0]
	if q == nil {
		return 1
	}
	return q.A // want `postcondition may not hold: r = 1`
}

// Counter counts, and writes behind its receiver as a Sink.
type Counter struct{ N int }

// @Requires c != nil And |p| <= 100
// @Modifies c
// @Ensures 0 <= n <= |p|
func (c *Counter) Put(p []byte) (n int) {
	if c.N < 1000 {
		c.N++
	}
	return 0
}

// Conv converts a counter to a Sink, which writes nothing yet.
//
// @Requires c != nil
// @Ensures s != nil
func Conv(c *Counter) (s Sink) {
	return c
}

// Factory makes a sink and a pair.
type Factory interface {
	// @Ensures s != nil And fresh(s) And p != nil And fresh(p)
	Make() (s Sink, p *Pair)
}

// MakeAndWrite relies on a new pair staying as it was across a write
// through a new sink, whose footprint is new and may hold it.
//
// @Requires f != nil
// @Ensures r = 5
func MakeAndWrite(f Factory) (r int) {
	s, p := f.Make()
	p.A = 5
	s.Put(nil)
	return p.A // want `postcondition may not hold: r = 5`
}

// Reuser makes a pair, and hands out a sink that may hold it.
type Reuser interface {
	// @Ensures s != nil And p != nil And fresh(p)
	Make() (s Sink, p *Pair)
}

// MakeOld relies on a new pair staying as it was across a write through a
// sink that may be an old value holding it.
//
// @Requires f != nil
// @Ensures r = 5
func MakeOld(f Reuser) (r int) {
	s, p := f.Make()
	p.A = 5
	s.Put(nil) // want `s.Put may modify the footprint of s, which MakeOld may not modify`
	return p.A // want `postcondition may not hold: r = 5`
}

// MayFail writes through s and then fails unless q.A is 1.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures err = nil <-> q.A = 1
func MayFail(s Sink, q *Pair) (err error) {
	s.Put(nil)
	if q.A != 1 {
		return errors.New("not one")
	}
	return nil
}

// Weak lets the function always fail: it says only that success means
// q.A is 1.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures err = nil -> q.A = 1
func Weak(s Sink, q *Pair) (err error) { // want `the contract of Weak may also be met by a function that always returns an error`
	s.Put(nil)
	if q.A != 1 {
		return errors.New("not one")
	}
	return nil
}
