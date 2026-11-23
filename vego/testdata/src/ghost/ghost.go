// Package ghost converts values of its own to interfaces whose contracts
// speak of a state: the states of such a value are ghost, start False, and
// are chosen after each call that changes them (F28).
package ghost

import (
	"errors"
	"io"
)

type quiet struct{}

// @Ensures err = nil
func (quiet) Close() (err error) { return nil }

// CloseQuiet converts a closer of its own and closes it.
//
// @Ensures True
func CloseQuiet() {
	var c io.Closer = quiet{}
	c.Close()
}

// CloseQuietTwice closes it twice.
//
// @Ensures True
func CloseQuietTwice() {
	var c io.Closer = quiet{}
	c.Close()
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// Shutter has a state of its own.
//
// @State shut
type Shutter interface {
	// Shut changes the state only.
	//
	// @Receiver s
	// @Requires ~shut(s)
	// @Modifies s
	// @Ensures shut(s')
	Shut()
}

// Stopper has a state, and a method that writes behind its receiver too.
//
// @State stopped
type Stopper interface {
	// Stop changes the state and may write what the value holds.
	//
	// @Receiver s
	// @Requires ~stopped(s)
	// @Modifies s, behind(s)
	// @Ensures stopped(s')
	Stop()
}

// Counter counts how often it was shut or stopped.
type Counter struct{ n int }

// @Requires c != nil
// @Modifies c
// @Ensures True
func (c *Counter) Shut() {
	if c.n < 1000 {
		c.n++
	}
}

// @Requires c != nil
// @Modifies c
// @Ensures True
func (c *Counter) Stop() {
	if c.n < 1000 {
		c.n++
	}
}

// ShutCounter converts it where the contract lists s alone, which a method
// that writes its struct does not meet.
//
// @Ensures True
func ShutCounter() {
	var s Shutter = &Counter{} // want `Shut may modify &Counter\{\}, which Shutter.Shut may not modify; the contract of Shutter.Shut lists s, which covers its states and nothing else; a method that also writes behind its receiver says so with behind\(s\) in Modifies`
	s.Shut()
}

// StopCounter converts it where the contract lists s and behind(s).
//
// @Ensures True
func StopCounter() {
	var s Stopper = &Counter{}
	s.Stop()
}

// StopForgets reads the counter after a Stop, which writes it.
//
// @Ensures n = 0
func StopForgets() (n int) {
	c := &Counter{}
	var s Stopper = c
	s.Stop()
	return c.n // want `postcondition may not hold: n = 0`
}

// Tx is a transaction of the project.
//
// @State open
type Tx interface {
	// @Receiver t
	// @Requires ~open(t)
	// @Modifies t, behind(t)
	// @Ensures (err = nil) <-> open(t')
	Begin() (err error)

	// @Receiver t
	// @Requires open(t)
	// @Modifies t, behind(t)
	// @Ensures ~open(t')
	Commit() (err error)

	// @Receiver t
	// @Requires open(t)
	// @Modifies t, behind(t)
	// @Ensures ~open(t')
	Rollback()
}

// memTx keeps what a transaction writes until it is committed.
//
// @Owns store, pending
type memTx struct {
	store   map[string]int
	pending map[string]int
	full    bool
}

// @Requires t != nil
// @Modifies t
// @Ensures ~t.full -> err = nil
func (t *memTx) Begin() (err error) {
	if t.full {
		return errors.New("full")
	}
	t.pending = map[string]int{}
	return nil
}

// @Requires t != nil
// @Modifies t
// @Ensures t.store != nil And t.pending != nil -> err = nil
func (t *memTx) Commit() (err error) {
	if t.store == nil || t.pending == nil {
		return errors.New("no store")
	}
	for k, v := range t.pending {
		t.store[k] = v
	}
	return nil
}

// @Requires t != nil
// @Modifies t
// @Ensures True
func (t *memTx) Rollback() {
	t.pending = nil
}

// Transact converts a transaction of its own, and commits it or rolls it
// back.
//
// @Ensures True
func Transact() (err error) {
	var t Tx = &memTx{store: map[string]int{}}
	if err := t.Begin(); err != nil {
		return err
	}
	if err := t.Commit(); err != nil {
		return err
	}
	return nil
}

// CommitUnbegun commits before Begin.
//
// @Ensures True
func CommitUnbegun() {
	var t Tx = &memTx{store: map[string]int{}}
	t.Commit() // want `precondition of t.Commit may not hold: open\(t\)`
}

// Peeker reads a state of its receiver without changing it.
//
// @State open
type Peeker interface {
	// @Receiver p
	// @Requires ~open(p)
	// @Modifies p
	// @Ensures open(p')
	Open()

	// @Receiver p
	// @Ensures open(p) -> n = 5
	Peek() (n int)
}

type six struct{}

// @Ensures True
func (six) Open() {}

// @Ensures n = 6
func (six) Peek() (n int) { return 6 }

// OpenThenPeek converts a value whose Peek cannot know the state.
//
// @Ensures n = 5
func OpenThenPeek() (n int) {
	var p Peeker = six{} // want `postcondition may not hold: open\(p\) -> n = 5`
	p.Open()
	return p.Peek()
}

// Knower says a state it cannot know.
//
// @State on
type Knower interface {
	// @Receiver k
	// @Ensures b <-> on(k)
	IsOn() (b bool)
}

type light struct{}

// @Ensures b = False
func (light) IsOn() (b bool) { return false }

// AskLight converts a value that claims to know its state.
//
// @Ensures True
func AskLight() {
	var k Knower = light{} // want `postcondition may not hold: b <-> on\(k\)`
	k.IsOn()
}

// forward closes by counting in a Counter it points to, which is not
// part of its footprint.
type forward struct{ to *Counter }

// @Requires f.to != nil
// @Modifies f.to
// @Ensures err = nil
func (f forward) Close() (err error) {
	f.to.Shut()
	return nil
}

// CloseForward converts a closer whose Close writes outside what it holds.
//
// @Ensures True
func CloseForward() {
	var c io.Closer = forward{to: &Counter{}} // want `Close may modify what it calls f.to, which Closer.Close may not modify; it is not part of the footprint of forward, which is empty`
	c.Close()
}

// Grabber closes what it is handed.
//
// @State held
type Grabber interface {
	// @Receiver g
	// @Requires o != nil And ~closed(o)
	// @Modifies g, o
	// @Ensures closed(o')
	Grab(o io.Closer)
}

type lazy struct{}

// @Ensures True
func (lazy) Grab(o io.Closer) {}

// GrabLazy converts a value whose Grab does not close what it is handed:
// only the states of the receiver are chosen.
//
// @Ensures True
func GrabLazy() {
	var g Grabber = lazy{} // want `postcondition may not hold for any value of the state held of g after the call: closed\(o'\)`
	_ = g
}
