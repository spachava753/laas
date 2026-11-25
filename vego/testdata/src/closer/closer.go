// Package closer replaces the shipped entry of (io.Closer).Close by one that
// says nothing of the state closed. io.NopCloser vouches that the Close of
// its result meets the entry of Close, so shipped entries rest on it, and a
// replacement must be the shipped entry itself (S0 of F35). This one keeps
// every shipped entry true, since NopCloser's Close writes nothing, and is
// refused all the same until what each wrapper delivers is computed (see
// the roadmap). What the programs here tested before is tested under the
// shipped entry in ifacestate, ghost, and the guide.
package closer

import (
	"io"
	"net/http"
)

// @Requires resp != nil And resp.Body != nil
// @Ensures True
func Done(resp *http.Response) (c int) {
	defer resp.Body.Close() // want `the trusted contract of \(io.Closer\).Close \(vego-trusted.yaml:4\) cannot be used: it replaces the shipped entry of \(io.Closer\).Close, on which shipped entries rest \(io.NopCloser vouches that the Close of its result meets it\), and it differs from it`
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
	return file{} // want `the trusted contract of \(io.Closer\).Close \(vego-trusted.yaml:4\) cannot be used: it replaces the shipped entry of \(io.Closer\).Close, on which shipped entries rest \(io.NopCloser vouches that the Close of its result meets it\), and it differs from it`
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

// The entry of Close cannot be used here, so verified code makes no
// io.Closer, and a trusted function that runs what a Record holds runs no
// code that verified code made.
//
// @Ensures s != nil
func MakeSink() (s Sink) {
	return logNumber
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
	two(c, file{}) // want `the trusted contract of \(io.Closer\).Close \(vego-trusted.yaml:4\) cannot be used: it replaces the shipped entry of \(io.Closer\).Close, on which shipped entries rest \(io.NopCloser vouches that the Close of its result meets it\), and it differs from it`
}
