// Package closer replaces the shipped entry of (io.Closer).Close by one that
// says nothing of the state closed. io.NopCloser vouches that the Close of
// its result meets the entry of Close, so shipped entries rest on it, and a
// replacement must be the shipped entry itself (S0 of F35). This one keeps
// every shipped entry true, since NopCloser's Close writes nothing, and is
// reported all the same until what each wrapper delivers is computed (see
// the roadmap); the shipped entry is used in its place, under which Done,
// which closed a body nothing says is open, is refused, and the rest is
// tested as before. What Done showed is tested under the shipped entry in
// ifacestate, ghost, and the guide (Status).
package closer

import (
	"io"
	"net/http"
)

// @Requires resp != nil And resp.Body != nil
// @Ensures True
func Done(resp *http.Response) (c int) {
	defer resp.Body.Close() // want `precondition of resp.Body.Close may not hold: ~closed\(c\)` `resp.Body.Close may modify the states of resp.Body, which Done may not modify`
	return resp.StatusCode
}

// file is a closer of the project, which converts to io.Closer under the
// shipped entry with states of its own (ghost states).
type file struct{}

// @Ensures err = nil
func (file) Close() (err error) {
	return nil
}

// @Ensures c != nil
func Make() (c io.Closer) {
	return file{}
}

// Record holds a closer.
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

// Verified code can make an io.Closer here, so a trusted function that runs
// what a Record holds may run code that verified code made.
//
// @Ensures s != nil
func MakeSink() (s Sink) {
	return logNumber // want `cannot verify MakeSink: logNumber may call through a function value or an interface value.*a value of io.Closer, whose methods all have contracts, so that it can hold code that verified code made`
}

// @Requires a != nil And b != nil
// @Ensures True
func two(a, b io.Closer) {}

// Two hands a made value beside a parameter to a function that changes
// the state of neither.
//
// @Requires c != nil
// @Ensures True
func Two(c io.Closer) {
	two(c, file{})
}
