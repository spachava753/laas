// Package p hands readers on where no entry can say what the code that
// gets them finds on them: a function of another package without an entry,
// and an interface whose contract is in source.
package p

import (
	"io"

	"cycles/claim/q"
)

// Feed is not verified, and hands what it holds to q.Plain, which has no
// entry.
type Feed struct{ r io.Reader }

func (f Feed) Read(b []byte) (int, error) { return q.Plain(f.r), nil }

// Through reads from a Feed through io.Reader; the cycle runs through
// q.Plain, which only an entry could narrow.
//
// @Requires r != nil
// @Ensures True
func Through(r io.Reader) (n int, err error) {
	return r.Read(make([]byte, 1)) // want `this call may not end: Through calls r.Read\(make\(\[\]byte, 1\)\) at p.go:\d+:\d+, which may run Feed.Read, Feed.Read hands f.r to q.Plain\(f.r\) at p.go:\d+:\d+, which may run Through; .*; cycles/claim/q.Plain has no entry that says what it finds on r; if it calls only the methods of io.Reader, give it an entry with "asserts: \{r: \[\]\}" in vego-trusted.yaml`
}

// Sink takes a reader; its contract is in source.
type Sink interface {
	// @Requires r != nil
	// @Ensures True
	Take(r io.Reader) (n int)
}

// Gives hands a reader to a Sink, whose implementation may be code of
// another package.
//
// @Requires s != nil And r != nil
// @Ensures True
func Gives(s Sink, r io.Reader) (n int) {
	return s.Take(r) // want `this call may not end: Gives hands r to s.Take\(r\) at p.go:\d+:\d+, which may run .*; the contract of \(cycles/claim2/p.Sink\).Take in source cannot say what its implementations find on r`
}
