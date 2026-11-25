package guide

import "io"

// The programs of the section "Methods that other code finds by a type
// assertion".

// Odometer counts what it is written, by Write and by WriteString.
type Odometer struct{ N int }

// @Requires t != nil
// @Modifies t
// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (t *Odometer) Write(p []byte) (n int, err error) {
	if t.N < 1000000 {
		t.N++
	}
	return len(p), nil
}

// @Requires t != nil
// @Modifies t
// @Ensures 0 <= n <= |s| And (n < |s| -> err != nil) And err = nil
func (t *Odometer) WriteString(s string) (n int, err error) {
	if t.N < 1000000 {
		t.N++
	}
	return len(s), nil
}

// @Requires t != nil
// @Modifies t
// @Ensures True
func Measure(t *Odometer) {
	_, _ = io.WriteString(t, "one line\n")
}

// LineOdometer counts lines by Write, and has a WriteString with no contract.
type LineOdometer struct{ N int }

// @Requires l != nil
// @Modifies l
// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (l *LineOdometer) Write(p []byte) (n int, err error) {
	if l.N < 1000000 {
		l.N++
	}
	return len(p), nil
}

// WriteString has no contract.
func (l *LineOdometer) WriteString(s string) (n int, err error) {
	return l.Write([]byte(s))
}

// @Requires l != nil
// @Modifies l
// @Ensures True
func MeasureLines(l *LineOdometer) {
	_, _ = io.WriteString(l, "one line\n") // want `cannot verify MeasureLines: converting a \*LineOdometer to io.Writer is not supported: \*LineOdometer implements io.StringWriter, whose method WriteString has an entry that io.WriteString relies on of every value it finds it on, and a value converted to io.Writer may be handed to it; \(\*LineOdometer\).WriteString has no contract; annotate it with // @ annotations that meet the entry of \(io.StringWriter\).WriteString, or rename it`
}

// WriteFast writes s through the WriteString of w where w has one.
//
// @Requires w != nil
// @Modifies w
// @Ensures 0 <= n <= |s|
func WriteFast(w io.Writer, s string) (n int) {
	if sw, ok := w.(io.StringWriter); ok {
		n, _ = sw.WriteString(s)
		return n
	}
	n, _ = w.Write([]byte(s))
	return n
}

// WriteAny asserts an any to io.Writer, which stays refused.
//
// @Requires v != nil
// @Ensures True
func WriteAny(v any) (n int) {
	if w, ok := v.(io.Writer); ok { // want `cannot verify WriteAny: using the value of v.\(io.Writer\) is not supported`
		n, _ = w.Write([]byte("x"))
	}
	return n
}
