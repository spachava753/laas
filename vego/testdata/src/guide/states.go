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
	return quiet{} // want `cannot verify Quiet: converting a value of type quiet to io.Closer is not supported yet: io.Closer has the state closed, and the contract of Closer.Close speaks of it; nothing ties a state to what the methods of quiet do until the memory a value owns is modelled, the next part of interfaces. Make the conversion in code that is not verified`
}

// Replace puts another body into a response.
//
// @Requires resp != nil
// @Modifies resp.Body
// @Ensures True
func Replace(resp *http.Response, body io.ReadCloser) {
	resp.Body = body // want `resp.Body is assigned, which Replace may not modify: // @Modifies resp.Body covers the states of what the interface value resp.Body holds, not the place that holds it; to assign it, list the struct that holds it`
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
