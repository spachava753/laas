package ghost

import (
	"bytes"
	"io"
)

// ShutBoth closes two values that a caller does not pass as one value or
// as a value and one whose methods change the states of the other.
//
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures closed(a') And closed(b')
func ShutBoth(a, b io.Closer) {
	a.Close()
	b.Close()
}

// WrapAndShut passes a closer and one that NopCloser made over it, whose
// footprint may hold the states of the first.
//
// @Requires x != nil And ~closed(x)
// @Modifies x
// @Ensures True
func WrapAndShut(x io.ReadCloser) {
	rc := io.NopCloser(x)
	ShutBoth(x, rc) // want `the interface values passed to ShutBoth as a and b may change each other's states`
}

// Two holds two closers in memory.
type Two struct{ A, B io.Closer }

// ShutHeld passes two closers read from memory.
//
// @Requires t != nil And t.A != nil And t.B != nil And ~closed(t.A) And ~closed(t.B)
// @Modifies t.A, t.B
// @Ensures True
func ShutHeld(t *Two) {
	ShutBoth(t.A, t.B) // want `the interface values passed to ShutBoth as a and b may share their states`
}

// Lid is a closer of the project that remembers that it was closed.
type Lid struct{ shut bool }

// @Requires l != nil
// @Modifies l
// @Ensures err = nil
func (l *Lid) Close() (err error) {
	l.shut = true
	return nil
}

// ShutBeside passes a converted closer of its own beside a parameter: its
// footprint is its struct, and its states are new.
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func ShutBeside(c io.Closer) {
	ShutBoth(io.Closer(&Lid{}), c)
}

// KeptAcrossWrite closes a converted closer after a write through another
// writer, which cannot have closed it: its home is new.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func KeptAcrossWrite(w io.Writer, p []byte) {
	var c io.Closer = quiet{}
	w.Write(p)
	c.Close()
}

// ClosedAcrossWrite closes it before the write and after it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func ClosedAcrossWrite(w io.Writer, p []byte) {
	var c io.Closer = quiet{}
	c.Close()
	w.Write(p)
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// Grew closes c and reports how much b grew meanwhile: a caller does not
// pass a closer that writes b beside b, as a gzip writer over b would.
//
// @Requires b != nil And c != nil And ~closed(c)
// @Modifies c
// @Ensures r = 0
func Grew(b *bytes.Buffer, c io.Closer) (r int) {
	n := b.Len()
	c.Close()
	return b.Len() - n
}

// Pair holds a buffer and a closer that may write it.
type Pair struct {
	B *bytes.Buffer
	C io.Closer
}

// GrewHeld closes p.C and reports how much p.B grew meanwhile, which a
// gzip writer over p.B makes 20: unsound before Close could write behind
// its receiver.
//
// @Requires p != nil And p.B != nil And p.C != nil And ~closed(p.C)
// @Modifies p.C
// @Ensures r = 0
func GrewHeld(p *Pair) (r int) {
	n := p.B.Len()
	p.C.Close()
	return p.B.Len() - n // want `precondition of Len may not hold: b != nil` `postcondition may not hold: r = 0`
}

// Opener has a method that does not list its receiver and says a state
// after the call, which its contract cannot: nothing it modifies holds the
// state, so the call cannot have changed it.
//
// @State live
type Opener interface {
	// @Receiver o
	// @Ensures live(o')
	Ping() // want `the contract of Opener.Ping cannot be used: its ensures "live\(o'\)" describes o' after the call` `the Ensures clauses of Opener.Ping are not proved to be satisfiable`
}
