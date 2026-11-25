// Package optionalio holds the programs of F35 that call io.WriteString and
// (*bufio.Writer).WriteString, which find the WriteString of what they are
// handed by asserting it to io.StringWriter, and the bounded copy that the
// messages for io.Copy name. It has no test file, so os.Stderr is assigned
// by nothing in its build.
package optionalio

import (
	"bufio"
	"io"
	"net/http"
	"os"
)

// Greet writes a greeting to w, whatever w is.
//
// @Requires w != nil And |name| <= 100
// @Modifies w
// @Ensures err = nil -> n = |name| + 7
func Greet(w io.Writer, name string) (n int, err error) {
	if n, err = io.WriteString(w, "hello, "); err != nil {
		return n, err
	}
	m, err := io.WriteString(w, name)
	return n + m, err
}

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
// @Ensures n = |s| And err = nil
func (t *Tally) WriteString(s string) (n int, err error) {
	if t.n < 1000000 {
		t.n++
	}
	return len(s), nil
}

// Lines counts lines.
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

// Both greets through a tally, which has WriteString, and a line counter,
// which has not, in that order, and then in the other.
//
// @Requires t != nil And l != nil
// @Modifies t, l
// @Ensures True
func Both(t *Tally, l *Lines) {
	_, _ = Greet(t, "a")
	_, _ = Greet(l, "b")
	_, _ = Greet(l, "c")
	_, _ = Greet(t, "d")
}

// ToStderr writes a line to standard error.
//
// @Ensures True
func ToStderr() (err error) {
	_, err = io.WriteString(os.Stderr, "done\n")
	return err
}

// ToFile writes a line to a file through a buffered writer, by WriteString,
// and flushes it.
//
// @Requires f != nil And |line| <= 1000
// @Ensures True
func ToFile(f *os.File, line string) (err error) {
	bw := bufio.NewWriter(f)
	if _, err = bw.WriteString(line); err != nil {
		return err
	}
	if _, err = bw.WriteString("\n"); err != nil {
		return err
	}
	return bw.Flush()
}

// Buffered writes through a buffered writer over w, whose WriteString the
// buffered writer calls for a string longer than its buffer when w has one.
//
// @Requires w != nil And |s| <= 100000
// @Modifies w
// @Ensures True
func Buffered(w io.Writer, s string) (err error) {
	bw := bufio.NewWriter(w)
	if _, err = bw.WriteString(s); err != nil {
		return err
	}
	return bw.Flush()
}

// BufferedTally hands Buffered a tally, converted at the call.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func BufferedTally(t *Tally) (err error) {
	return Buffered(t, "a string")
}

// Kept writes through a buffered writer it is handed.
//
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures ready(bw')
func Kept(bw *bufio.Writer) (n int, err error) {
	return bw.WriteString("kept")
}

// Fan writes one string to two writers through io.MultiWriter, whose
// WriteString io.WriteString finds.
//
// @Requires a != nil And b != nil
// @Modifies a, b
// @Ensures True
func Fan(a, b io.Writer) (err error) {
	_, err = io.WriteString(io.MultiWriter(a, b), "both")
	return err
}

// Handle answers a request through the writer of its response.
//
// @Requires w != nil And req != nil
// @Modifies w
// @Ensures True
func Handle(w http.ResponseWriter, req *http.Request) {
	_, _ = io.WriteString(w, "ok\n")
}

// Faster writes s through the WriteString of w where w has one, as
// io.WriteString does, which an io.Writer allows since every value
// converted to it was checked against io.StringWriter.
//
// @Requires w != nil
// @Modifies w
// @Ensures 0 <= n <= |s|
func Faster(w io.Writer, s string) (n int) {
	if sw, ok := w.(io.StringWriter); ok {
		n, _ = sw.WriteString(s)
		return n
	}
	n, _ = w.Write([]byte(s))
	return n
}

// put is trusted: it writes s to w, through WriteString when w has one. Its
// entry lists io.StringWriter under asserts, which F35 allows over an
// io.Writer.
func put(w io.Writer, s string) {
	if sw, ok := w.(io.StringWriter); ok {
		sw.WriteString(s)
		return
	}
	w.Write([]byte(s))
}

// UsesPut hands put a tally.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func UsesPut(t *Tally) {
	put(t, "x")
}

// CopySome copies from src to dst in at most 1000 reads of 4096 bytes, the
// loop that the messages for io.Copy, io.CopyN, and io.ReadAll name.
//
// @Requires dst != nil And src != nil
// @Modifies dst, src
// @Ensures 0 <= written <= 4096000
func CopySome(dst io.Writer, src io.Reader) (written int, err error) {
	buf := make([]byte, 4096)
	// @Invariant 0 <= i And i <= 1000 And 0 <= written And written <= 4096 * i
	// @Variant 1000 - i
	for i := 0; i < 1000; i++ {
		n, rerr := src.Read(buf)
		if n > 0 {
			m, werr := dst.Write(buf[:n])
			written += m
			if werr != nil {
				return written, werr
			}
		}
		if rerr == io.EOF {
			return written, nil
		}
		if rerr != nil {
			return written, rerr
		}
	}
	return written, nil
}

// Files copies one open file to another.
//
// @Requires from != nil And to != nil
// @Ensures True
func Files(from, to *os.File) (err error) {
	_, err = CopySome(to, from)
	return err
}

// Echo writes the body of a request to the writer of its response.
//
// @Requires w != nil And req != nil And req.Body != nil
// @Modifies w, req.Body
// @Ensures True
func Echo(w http.ResponseWriter, req *http.Request) {
	_, _ = CopySome(w, req.Body)
}
