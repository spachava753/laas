package optional

import (
	"bufio"
	"fmt"
	"io"
	"strings"

	"optionalc"
)

// Counter has a WriteString with no contract.
type Counter struct{ n int }

// @Requires c != nil
// @Modifies c
// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (c *Counter) Write(p []byte) (n int, err error) {
	if c.n < 1000000 {
		c.n++
	}
	return len(p), nil
}

// WriteString has no contract.
func (c *Counter) WriteString(s string) (n int, err error) { return -1, nil }

// @Requires c != nil
// @Modifies c
// @Ensures True
func CounterAsWriter(c *Counter) (n int) {
	var w io.Writer = c // want `cannot verify CounterAsWriter: converting a \*Counter to io.Writer is not supported: \*Counter implements io.StringWriter, whose method WriteString has an entry that .* relies on of every value it finds it on, and a value converted to io.Writer may be handed to it; \(\*Counter\).WriteString has no contract; annotate it with // @ annotations that meet the entry of \(io.StringWriter\).WriteString, or rename it`
	n, _ = w.Write([]byte("x"))
	return n
}

// @Ensures w != nil
func BadAsWriter() (w io.Writer) {
	return Bad{} // want `postcondition may not hold: n <= \|s\|, in Bad.WriteString used as a method of io.StringWriter at refused.go:\d+:\d+, which Bad implements: .* finds WriteString by a type assertion; meet the entry of \(io.StringWriter\).WriteString, or rename the method`
}

// inner has a WriteString that Outer gets from it.
type inner struct{}

// @Ensures 0 <= n <= |s| And (n < |s| -> err != nil) And err = nil
func (inner) WriteString(s string) (n int, err error) { return len(s), nil }

// Outer has a Write of its own and a promoted WriteString.
type Outer struct {
	inner
}

// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (Outer) Write(p []byte) (n int, err error) { return len(p), nil }

// @Ensures w != nil
func OuterAsWriter() (w io.Writer) {
	return Outer{} // want `cannot verify OuterAsWriter: converting an Outer to io.Writer is not supported: Outer implements io.StringWriter, .*; Outer gets WriteString from an embedded field, and a promoted method cannot be used as a method of an interface yet; rename the method, or give Outer a method WriteString of its own that meets the entry`
}

// Hits counts.
type Hits struct{ N int }

// Logged counts what WriteString is given in a Hits it points to, outside
// what a value of it holds.
type Logged struct{ hits *Hits }

// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (Logged) Write(p []byte) (n int, err error) { return len(p), nil }

// @Requires l.hits != nil
// @Modifies l.hits
// @Ensures 0 <= n <= |s| And (n < |s| -> err != nil) And err = nil
func (l Logged) WriteString(s string) (n int, err error) {
	if l.hits.N < 100 {
		l.hits.N++
	}
	return len(s), nil
}

// @Requires hits != nil
// @Ensures w != nil
func LoggedAsWriter(hits *Hits) (w io.Writer) {
	return Logged{hits: hits} // want `in Logged.WriteString used as a method of io.StringWriter`
}

// Quiet writes nothing behind its receiver in Write, and its WriteString
// counts (F5 of the design review: the footprint of a conversion is what
// every checked method may write).
type Quiet struct{ N int }

// @Requires q != nil
// @Ensures n = |p| And err = nil
func (q *Quiet) Write(p []byte) (n int, err error) { return len(p), nil }

// @Requires q != nil
// @Modifies q
// @Ensures 0 <= n <= |s| And (n < |s| -> err != nil) And err = nil
func (q *Quiet) WriteString(s string) (n int, err error) {
	if q.N < 100 {
		q.N++
	}
	return len(s), nil
}

// KeepsN converts q, writes a string through it, and claims that q.N is
// what it was. It is not proved: put finds WriteString.
//
// @Requires q != nil
// @Modifies q
// @Ensures r
func KeepsN(q *Quiet) (r bool) {
	before := q.N
	_ = put(q, "x")
	return q.N == before // want `postcondition may not hold: r`
}

// Pipe reads and writes; its Write breaks the entry of (io.Writer).Write,
// so converting it to io.Reader, which does not have Write, is refused.
type Pipe struct{}

// @Requires |p| > 0
// @Ensures n = 0 And err = nil
func (Pipe) Read(p []byte) (n int, err error) { return 0, nil }

// @Ensures n = -1 And err = nil
func (Pipe) Write(p []byte) (n int, err error) { return -1, nil }

// @Ensures r != nil
func PipeAsReader() (r io.Reader) {
	return Pipe{} // want `postcondition may not hold: 0 <= n, in Pipe.Write used as a method of io.Writer`
}

// RecMaybeNil converts a Rec that may be nil: the check fails once in the
// package and again here.
//
// @Ensures True
func RecMaybeNil(r *optionalc.Rec) (w io.Writer) {
	return r // want `precondition of WriteString may not hold: r != nil, in \(\*optionalc.Rec\).WriteString used as a method of io.StringWriter`
}

// OverAsWriter converts a writer of another module whose WriteString
// breaks the entry of io.StringWriter.
//
// @Ensures w != nil
func OverAsWriter() (w io.Writer) {
	return optionalc.Over{} // want `postcondition may not hold: n <= \|s\|, in optionalc.Over.WriteString used as a method of io.StringWriter`
}

// KeepsAcrossWrite writes through q's Write, which writes nothing, and
// claims that q.N is what it was, which is true. It is not proved: the
// footprint of the conversion is what every method checked at it may
// write, WriteString's included, and Write lists the footprint (F15 of the
// review of S1, a narrowing accepted by the orchestrator; a footprint per
// method would lift it).
//
// @Ensures r = 0
func KeepsAcrossWrite() (r int) {
	q := &Quiet{}
	var w io.Writer = q
	_, _ = w.Write([]byte("x"))
	return q.N // want `postcondition may not hold: r = 0`
}

// KeepsNThroughWriteString hands q to io.WriteString, which finds its
// WriteString: q.N is not proved unchanged (attack 1 of the design).
//
// @Requires q != nil
// @Modifies q
// @Ensures r
func KeepsNThroughWriteString(q *Quiet) (r bool) {
	before := q.N
	_, _ = io.WriteString(q, "x")
	return q.N == before // want `postcondition may not hold: r`
}

// bufferLong writes a long string through a buffered writer over w, which
// hands it to w's WriteString when w has one.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func bufferLong(w io.Writer) {
	bw := bufio.NewWriter(w)
	_, _ = bw.WriteString(strings.Repeat("x", 5000))
}

// KeepsNBuffered hands q to bufferLong: q.N is not proved unchanged.
//
// @Requires q != nil
// @Modifies q
// @Ensures r
func KeepsNBuffered(q *Quiet) (r bool) {
	before := q.N
	bufferLong(q)
	return q.N == before // want `postcondition may not hold: r`
}

// putLit is trusted; its entry lists an interface literal with the method
// set of io.StringWriter, whose WriteString is no method of a member of O.
func putLit(w io.Writer, s string) {
	if sw, ok := w.(interface{ WriteString(string) (int, error) }); ok {
		sw.WriteString(s)
	}
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func UsesPutLit(w io.Writer) {
	putLit(w, "x") // want `the trusted contract of optional.putLit \(trusted.yaml:\d+\) cannot be used: its asserts lists interface\{ WriteString\(string\) \(int, error\) \} for w, an interface with the method WriteString, and what it holds may hold a value of io.Writer, which lacks it`
}

// putAny is trusted; its entry lists io.Writer over an any, which is not
// O-typed.
func putAny(x any) {
	if w, ok := x.(io.Writer); ok {
		w.Write([]byte("x"))
	}
}

// @Requires x != nil
// @Ensures True
func UsesPutAny(x any) {
	putAny(x) // want `the trusted contract of optional.putAny \(trusted.yaml:\d+\) cannot be used: its asserts lists io.Writer for x, an interface with the method Write, and what it holds may hold a value of any, which lacks it`
}

// Pair holds a writer and a stringer: the second is not O-typed.
type Pair struct {
	W io.Writer
	S fmt.Stringer
}

// putPair is trusted; its entry lists io.StringWriter over a Pair, which
// reaches a fmt.Stringer, which lacks WriteString and is not O-typed (the
// shape of runsclaims.HandsTwo).
func putPair(p Pair) {}

// @Requires p.W != nil
// @Modifies p.W
// @Ensures True
func UsesPutPair(p Pair) {
	putPair(p) // want `the trusted contract of optional.putPair \(trusted.yaml:\d+\) cannot be used: its asserts lists io.StringWriter for p, an interface with the method WriteString, and what it holds may hold a value of fmt.Stringer, which lacks it`
}
