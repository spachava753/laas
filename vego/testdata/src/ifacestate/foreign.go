package ifacestate

import (
	"io"

	"ifacestatelib"
)

// Get closes the body of a response it fetched: the body is new, so
// closing it changes nothing a caller can see.
//
// @Ensures True
func Get() (status int, err error) {
	resp, err := ifacestatelib.Fetch("x")
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()
	return resp.Status, nil
}

// GetStale closes a body that may be one a caller holds.
//
// @Ensures True
func GetStale() (status int, err error) {
	resp, err := ifacestatelib.Stale("x")
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close() // want `resp.Body.Close may modify the states of resp.Body, which GetStale may not modify`
	return resp.Status, nil
}

// Connect runs the protocol of a connection, which Abort keeps.
//
// @Requires c != nil And ~started(c)
// @Modifies c
// @Ensures ~started(c')
func Connect(c ifacestatelib.Conn) (err error) {
	if err := c.Start(); err != nil {
		return err
	}
	c.Abort()
	return c.Finish()
}

// FinishUnstarted finishes a connection that may not be open.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func FinishUnstarted(c ifacestatelib.Conn) (err error) {
	return c.Finish() // want `precondition of c.Finish may not hold: started\(c\)`
}

// Pinged pings a wrapped connection, which keeps it open.
//
// @Requires w != nil And started(w)
// @Modifies w
// @Ensures ~started(w')
func Pinged(w ifacestatelib.Wrapped) (err error) {
	w.Ping()
	return w.Finish()
}

// Consumed hands a reader to a function that may close it.
//
// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures True
func Consumed(rc io.ReadCloser) (err error) {
	ifacestatelib.Consume(rc)
	return rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\)`
}

// ConsumedUnlisted hands a reader on without listing it.
//
// @Requires r != nil
// @Ensures True
func ConsumedUnlisted(r io.Reader) {
	ifacestatelib.Consume(r) // want `Consume may modify the states of r, which ConsumedUnlisted may not modify`
}

// Record holds a closer, which verified code cannot make under the shipped
// entry, whose contract speaks of the state closed.
type Record struct {
	N int
	C io.Closer
}

func logCloser(r Record) {}

// Sink takes a number.
//
// @Ensures True
type Sink func(x int)

// @Ensures True
func logNumber(x int) {
	var r Record
	r.N = x
	logCloser(r)
}

// MakeSink makes a value of a function that hands a closer to a trusted
// function that runs it. Verified code makes no io.Closer, so nothing the
// trusted function runs is code that verified code made.
//
// @Ensures s != nil
func MakeSink() (s Sink) {
	return logNumber
}

func receiverNamed() {}

// UsesReceiverNamed calls a trusted function whose entry names a receiver.
//
// @Ensures True
func UsesReceiverNamed() {
	receiverNamed() // want `it names a receiver, which only an entry for a method of an interface can do` `cannot verify UsesReceiverNamed: receiverNamed has a contract that could not be understood`
}

// GetThenClose closes a new body and then a parameter, whose home the new
// one cannot be.
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures closed(c')
func GetThenClose(c io.Closer) (err error) {
	resp, err := ifacestatelib.Fetch("x")
	if err == nil {
		resp.Body.Close()
	}
	return c.Close()
}
