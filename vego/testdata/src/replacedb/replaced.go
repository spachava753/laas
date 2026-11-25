// Package replacedb replaces two shipped entries that other shipped entries
// rest on by entries that differ from them, each of which made a proof
// false before S0 of F35. Each replacement is reported at the trust file,
// and the shipped entry is used in its place.
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
// writer returns, and panics on a count past it. Under the shipped entry of
// Write the conversion of Over is refused.
//
// @Ensures True
func Flushes() (err error) {
	var w io.Writer = Over{} // want `postcondition may not hold: n <= \|p\|, in Over.Write used as a method of io.Writer`
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
	_, err := tr.Read(make([]byte, 8))
	a = errors.Is(err, io.EOF) // want `cannot verify Twice: errors.Is would run the Is and Unwrap methods of err, an error whose origin is not known`
	b = errors.Is(err, io.EOF)
	return a, b
}

// FlushesParam writes through a buffered writer over a writer its caller
// hands it, so nothing here converts a writer or calls the entry of Write:
// a replacement reported only where its entry is looked up would let it
// verify with the shipped (*bufio.Writer).Write resting on the replacement
// unseen (F11 of the review of S0 of F35). The replacement is reported at
// the trust file whatever the package looks up, and the shipped entry of
// Write stands, under which it verifies: a caller that hands it an Over
// breaks the shipped entry's claim about writers from code that is not
// verified, as run_test.go shows.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func FlushesParam(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	if _, err = bw.Write(make([]byte, 5000)); err != nil {
		return err
	}
	return bw.Flush()
}
