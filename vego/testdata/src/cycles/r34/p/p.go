// r34: a writer of the package handed as an argument through a call of an
// interface method, whose implementation may be code of another package.
package p

import "io"

// Sink takes a writer.
type Sink interface {
	// @Requires w != nil
	// @Ensures True
	Take(w io.Writer) (n int)
}

// W writes by calling F.
type W struct{ S Sink }

func (w W) Write(p []byte) (int, error) { F(w.S, w); return len(p), nil }

// @Requires s != nil And w != nil
// @Ensures True
func F(s Sink, w io.Writer) (n int) {
	return s.Take(w) // want `this\ call\ may\ not\ end:\ F\ hands\ w\ to\ s\.Take\(w\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ F`
}
