// Package replacedb replaces two shipped entries that other shipped entries
// rest on by entries that differ from them, each of which made a proof
// false before S0 of F35.
package replacedb

import (
	"bufio"
	"errors"
	"io"
)

// Over reports more bytes than it was given, which the weaker replacement
// of Write allows.
type Over struct{}

// @Ensures n = |p| + 1 And err = nil
func (Over) Write(p []byte) (n int, err error) { return len(p) + 1, nil }

// Flushes writes 5000 bytes through a buffered writer over an Over. The
// Write of the buffered writer slices what it is given by the count its
// writer returns, and panics on a count past it.
//
// @Ensures True
func Flushes() (err error) {
	var w io.Writer = Over{} // want `the trusted contract of \(io.Writer\).Write \(vego-trusted.yaml:12\) cannot be used: it replaces the shipped entry of \(io.Writer\).Write, on which shipped entries rest`
	bw := bufio.NewWriter(w)
	if _, err = bw.Write(make([]byte, 5000)); err != nil {
		return err
	}
	return bw.Flush()
}

// Twice asks errors.Is twice of the error of the Read of a tee. The
// replacement of Read vouches for its errors, and the result of
// io.TeeReader returns the errors of the writer's Write, which nothing
// vouches for.
//
// @Requires r != nil And w != nil
// @Modifies r, w
// @Ensures a = b
func Twice(r io.Reader, w io.Writer) (a, b bool) {
	tr := io.TeeReader(r, w)
	_, err := tr.Read(make([]byte, 8)) // want `the trusted contract of \(io.Reader\).Read \(vego-trusted.yaml:17\) cannot be used: it replaces the shipped entry of \(io.Reader\).Read`
	a = errors.Is(err, io.EOF)
	b = errors.Is(err, io.EOF)
	return a, b
}
