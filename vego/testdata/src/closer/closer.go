// Package closer closes the body of a response under a project entry for
// (io.Closer).Close, which vego does not ship.
package closer

import (
	"io"
	"net/http"
)

// @Requires resp != nil And resp.Body != nil
// @Ensures True
func Done(resp *http.Response) (c int) {
	defer resp.Body.Close()
	return resp.StatusCode
}

// file is a closer of the project, which can be converted to io.Closer
// under the entry of this module: it names no receiver, so its contract
// says nothing of the state closed.
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
	return logNumber // want `cannot verify MakeSink: logNumber may call through a function value or an interface value.*a value of io.Closer, whose methods all have contracts, so that verified code can make one`
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
