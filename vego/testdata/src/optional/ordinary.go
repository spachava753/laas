// Package optional holds the conversions that F35 checks against the
// interfaces of O, the interfaces whose every method has a trust entry and
// which have no states and are not scoped, and the assertions and entries
// that lean on the check. This file holds what a user writes first; the
// refusals and the attacks are in refused.go and attacks.go.
package optional

import (
	"io"
	"optionalc"
	"os"
)

// Tally counts what it is given, through Write and WriteString alike.
type Tally struct{ n int }

// @Requires t != nil
// @Modifies t
// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (t *Tally) Write(p []byte) (n int, err error) {
	if t.n < 1000000 {
		t.n++
	}
	return len(p), nil
}

// @Requires t != nil
// @Modifies t
// @Ensures 0 <= n <= |s| And (n < |s| -> err != nil) And err = nil
func (t *Tally) WriteString(s string) (n int, err error) {
	if t.n < 1000000 {
		t.n++
	}
	return len(s), nil
}

// Lines counts lines, by Write and by WriteString.
type Lines struct{ lines int }

// @Requires l != nil
// @Modifies l
// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (l *Lines) Write(p []byte) (n int, err error) {
	if l.lines < 1000000 {
		l.lines++
	}
	return len(p), nil
}

// @Requires l != nil
// @Modifies l
// @Ensures 0 <= n <= |s| And (n < |s| -> err != nil) And err = nil
func (l *Lines) WriteString(s string) (n int, err error) {
	if l.lines < 1000000 {
		l.lines++
	}
	return len(s), nil
}

// put writes s through w, by WriteString where w has it, as io.WriteString
// does.
//
// @Requires w != nil
// @Modifies w
// @Ensures 0 <= n <= |s|
func put(w io.Writer, s string) (n int) {
	if sw, ok := w.(io.StringWriter); ok {
		n, _ = sw.WriteString(s)
		return n
	}
	n, _ = w.Write([]byte(s))
	return n
}

// Both writes through a tally and a line counter, in that order.
//
// @Requires t != nil And l != nil
// @Modifies t, l
// @Ensures 0 <= n <= 2
func Both(t *Tally, l *Lines) (n int) {
	n = put(t, "a")
	n += put(l, "b")
	return n
}

// BothSwapped writes through the line counter first.
//
// @Requires t != nil And l != nil
// @Modifies t, l
// @Ensures 0 <= n <= 2
func BothSwapped(t *Tally, l *Lines) (n int) {
	n = put(l, "b")
	n += put(t, "a")
	return n
}

// Local converts a tally it makes and writes through it.
//
// @Ensures 0 <= n <= 3
func Local() (n int) {
	var w io.Writer = &Tally{}
	return put(w, "abc")
}

// ToFiles writes a string to two files, whose WriteString the shipped
// entry of (*os.File).WriteString covers.
//
// @Requires f != nil And g != nil
// @Ensures 0 <= n <= 2
func ToFiles(f, g *os.File) (n int) {
	n = put(f, "x")
	n += put(g, "y")
	return n
}

// Odd has a WriteString of another signature, so it does not implement
// io.StringWriter, and nothing checks it; Go's assertion agrees
// (run_test.go).
type Odd struct{}

// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (Odd) Write(p []byte) (n int, err error) { return len(p), nil }

// WriteString of another signature.
func (Odd) WriteString(s string) int { return -1 }

// @Ensures ~ok
func OddAsks() (ok bool) {
	var w io.Writer = Odd{}
	_, ok = w.(io.StringWriter)
	return ok
}

// Bad's WriteString breaks the entry of io.StringWriter.
type Bad struct{}

// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (Bad) Write(p []byte) (n int, err error) { return len(p), nil }

// @Ensures n = |s| + 1 And err = nil
func (Bad) WriteString(s string) (n int, err error) { return len(s) + 1, nil }

// BadToAny converts a Bad to any, which is not O-typed, so the conversion
// is not checked; nothing can assert the any to an interface of O and use
// what it finds.
//
// @Ensures a != nil
func BadToAny() (a any) {
	return Bad{}
}

// Counts owns a map of what it was given; WriteString adds a key, which
// grows what the struct owns.
//
// @Owns m
type Counts struct {
	m map[string]int
}

// @Requires c != nil
// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (c *Counts) Write(p []byte) (n int, err error) {
	return len(p), nil
}

// @Requires c != nil
// @Modifies c
// @Ensures 0 <= n <= |s| And (n < |s| -> err != nil) And err = nil
func (c *Counts) WriteString(s string) (n int, err error) {
	if c.m == nil {
		c.m = make(map[string]int)
	}
	c.m[s] = 1
	return len(s), nil
}

// CountTwice converts an owner it makes and writes through it twice.
//
// @Ensures True
func CountTwice() {
	c := &Counts{}
	var w io.Writer = c
	_ = put(w, "a")
	_ = put(w, "b")
}

// RecAsWriter converts a writer of another module whose WriteString needs
// its receiver not nil. The check of WriteString once in the package, which
// knows nothing of the receiver, fails, and the check at this conversion,
// which knows that the pointer is not nil, passes (D6 of F35).
//
// @Ensures w != nil
func RecAsWriter() (w io.Writer) {
	return &optionalc.Rec{}
}
