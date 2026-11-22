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
	ifacestatelib.Consume(rc) // want `this\ call\ may\ not\ end:\ Consumed\ hands\ rc\ to\ ifacestatelib\.Consume\(rc\)\ at\ foreign\.go:\d+:\d+,\ which\ may\ run\ Consumed`
	return rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\)`
}

// ConsumedUnlisted hands a reader on without listing it.
//
// @Requires r != nil
// @Ensures True
func ConsumedUnlisted(r io.Reader) {
	ifacestatelib.Consume(r) // want `Consume may modify the footprint of r, which ConsumedUnlisted may not modify` `Consume may modify the states of r, which ConsumedUnlisted may not modify` `this\ call\ may\ not\ end:\ ConsumedUnlisted\ hands\ r\ to\ ifacestatelib\.Consume\(r\)\ at\ foreign\.go:\d+:\d+,\ which\ may\ run\ ConsumedUnlisted`
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
// function that runs it. Verified code converts nothing to io.Closer under
// the shipped entry, whose contract speaks of the state closed, but a
// trusted function that keeps what it is given, such as io.NopCloser, can
// put code that verified code made into one. So logCloser counts as a call
// through a value, and MakeSink, which verified before trusted functions
// that keep a value, is refused.
//
// @Ensures s != nil
func MakeSink() (s Sink) {
	return logNumber // want `cannot verify MakeSink: logNumber may call through a function value or an interface value.*logCloser, which is trusted and runs what r holds, which can be a value of io.Closer, whose methods all have contracts, so that it can hold code that verified code made`
}

func receiverNamed() {}

// UsesReceiverNamed calls a trusted function whose entry names a receiver.
//
// @Ensures True
func UsesReceiverNamed() {
	receiverNamed() // want `it names a receiver, which only an entry for a method of an interface can do`
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
