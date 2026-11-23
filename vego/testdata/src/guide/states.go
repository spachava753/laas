package guide

import (
	"io"
	"net/http"
	"os"
)

// The programs of the section on states of interface values.

// ReadOnce reads once into buf and closes rc.
//
// @Requires rc != nil And ~closed(rc) And |buf| > 0
// @Modifies rc, buf
// @Ensures closed(rc') And 0 <= n <= |buf|
func ReadOnce(rc io.ReadCloser, buf []byte) (n int, err error) {
	defer rc.Close()
	return rc.Read(buf)
}

// CloseTwice closes c twice.
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func CloseTwice(c io.Closer) {
	c.Close()
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// Status closes the body of a response it is given.
//
// @Requires resp != nil And resp.Body != nil And ~closed(resp.Body)
// @Modifies resp.Body
// @Ensures closed(resp.Body')
func Status(resp *http.Response) (code int) {
	defer resp.Body.Close()
	return resp.StatusCode
}

// ShutBoth closes two values.
//
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures closed(a') And closed(b')
func ShutBoth(a, b io.Closer) {
	a.Close()
	b.Close()
}

// ShutWithBody hands ShutBoth a body and a closer it is given.
//
// @Requires resp != nil And resp.Body != nil And c != nil
// @Requires ~closed(resp.Body) And ~closed(c)
// @Modifies resp.Body, c
// @Ensures True
func ShutWithBody(resp *http.Response, c io.Closer) {
	ShutBoth(resp.Body, c) // want `the interface values passed to ShutBoth as a and b may share their states: they may be one value, hold one value, or hold a value and one that wraps it, and ShutBoth may rely on them not doing so`
}

// open is trusted; see the trust file of the tests.
func open(name string) (rc io.ReadCloser, err error) {
	return os.Open(name)
}

// FirstByte reads the first byte of a file and closes it.
//
// @Ensures True
func FirstByte(name string) (b byte, err error) {
	rc, err := open(name)
	if err != nil {
		return 0, err
	}
	defer rc.Close()
	buf := make([]byte, 1)
	if _, err := rc.Read(buf); err != nil {
		return 0, err
	}
	return buf[0], nil
}

// Tx is a transaction whose state open its methods change.
//
// @State open
type Tx interface {
	// Begin starts the transaction.
	//
	// @Receiver t
	// @Requires ~open(t)
	// @Modifies t
	// @Ensures (err = nil) <-> open(t')
	Begin() (err error)

	// Commit ends it.
	//
	// @Receiver t
	// @Requires open(t)
	// @Modifies t
	// @Ensures ~open(t')
	Commit() (err error)
}

// Transact begins and commits.
//
// @Requires t != nil And ~open(t)
// @Modifies t
// @Ensures ~open(t')
func Transact(t Tx) (err error) {
	if err := t.Begin(); err != nil {
		return err
	}
	return t.Commit()
}

// CommitTwice commits a transaction that the first Commit ended.
//
// @Requires t != nil And open(t)
// @Modifies t
// @Ensures True
func CommitTwice(t Tx) {
	t.Commit()
	t.Commit() // want `precondition of t.Commit may not hold: open\(t\)`
}

// quiet is a closer of its own.
type quiet struct{}

// @Ensures err = nil
func (quiet) Close() (err error) {
	return nil
}

// @Ensures c != nil
func Quiet() (c io.Closer) {
	return quiet{}
}

// @Ensures True
func CloseQuietTwice() {
	var c io.Closer = quiet{}
	c.Close()
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// Shutter is shut once.
//
// @State shut
type Shutter interface {
	// Shut changes the state and nothing else.
	//
	// @Receiver s
	// @Requires ~shut(s)
	// @Modifies s
	// @Ensures shut(s')
	Shut()
}

// Stopper is stopped once.
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

// Lamp remembers that it was turned off.
type Lamp struct{ off bool }

// @Requires w != nil
// @Modifies w
// @Ensures True
func (w *Lamp) Shut() {
	w.off = true
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func (w *Lamp) Stop() {
	w.off = true
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

// @Ensures True
func AskLight() {
	var k Knower = light{} // want `postcondition may not hold: b <-> on\(k\), in light.IsOn used as a method of Knower at states.go:\d+:\d+`
	k.IsOn()
}

// @Ensures True
func ShutLamp() {
	var s Shutter = &Lamp{} // want `Shut may modify &Lamp\{\}, which Shutter.Shut may not modify; the contract of Shutter.Shut lists s, which covers its states and nothing else; a method that also writes behind its receiver says so with behind\(s\) in Modifies, in \(\*Lamp\).Shut used as a method of Shutter at states.go:\d+:\d+`
	s.Shut()
}

// @Ensures True
func StopLamp() {
	var s Stopper = &Lamp{}
	s.Stop()
}

// Job holds the closer it writes its output to.
type Job struct {
	Out io.Closer
}

// Replace puts another closer into a job.
//
// @Requires j != nil
// @Modifies j.Out
// @Ensures True
func Replace(j *Job, c io.Closer) {
	j.Out = c // want `j.Out is assigned, which Replace may not modify: // @Modifies j.Out covers the states of what the interface value j.Out holds, not the place that holds it; to assign it, list the struct that holds it`
}

// ReplaceBody puts a body it was handed into a response.
//
// @Requires resp != nil
// @Modifies resp
// @Ensures True
func ReplaceBody(resp *http.Response, body io.ReadCloser) {
	resp.Body = body // want `cannot verify ReplaceBody: resp.Body is stored into, and what the field Body of a net/http.Response holds writes nothing else the Response reaches`
}

// Limits holds a limit.
type Limits struct {
	Max int
}

// SetMax sets the limit and says so of the state on entry.
//
// @Requires l != nil And l.Max = 7
// @Modifies l.Max
// @Ensures l.Max = 7 // want `the Ensures clause "l.Max = 7" names no result and nothing on return, so it speaks of the state when SetMax is called, and it reads memory that SetMax may modify; write a prime for the value on return, as in l.Max', or move the clause to a Requires`
func SetMax(l *Limits) {
	l.Max = 7
}
