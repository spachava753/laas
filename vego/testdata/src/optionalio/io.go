// Package optionalio holds the programs of F35 that call io.WriteString and
// (*bufio.Writer).WriteString, which find the WriteString of what they are
// handed by asserting it to io.StringWriter, and the bounded copy that the
// messages for io.Copy name. It has no test file, so os.Stderr is assigned
// by nothing in its build.
package optionalio

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"
	"log"
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

// The programs of F20 of the review of S2 of F35: a WriteCloser written and
// then closed, whichever way the write is spelled.

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func ByWrite(wc io.WriteCloser) (err error) {
	_, _ = wc.Write([]byte("x"))
	return wc.Close()
}

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func ByWriteString(wc io.WriteCloser) (err error) {
	_, _ = io.WriteString(wc, "x")
	return wc.Close()
}

// @Requires wc != nil And ~closed(wc) And 0 <= n <= 1000
// @Modifies wc
// @Ensures True
func ByFprintf(wc io.WriteCloser, n int) (err error) {
	_, _ = fmt.Fprintf(wc, "%d\n", n)
	return wc.Close()
}

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func Deferred(wc io.WriteCloser) {
	defer wc.Close()
	_, _ = io.WriteString(wc, "x")
}

// Encoded encodes into wc in place and closes it: the encoder keeps the
// states of what it writes through.
//
// @Requires wc != nil And ~closed(wc) And 0 <= n <= 1000
// @Modifies wc
// @Ensures True
func Encoded(wc io.WriteCloser, n int) (err error) {
	_ = json.NewEncoder(wc).Encode(n)
	return wc.Close()
}

// TwoClosers writes two closers in one order and closes them in the other.
//
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures True
func TwoClosers(a, b io.WriteCloser) {
	_, _ = io.WriteString(a, "a")
	_, _ = fmt.Fprintf(b, "%d", 1)
	_ = b.Close()
	_, _ = io.WriteString(a, "again")
	_ = a.Close()
}

// TwoClosersSwapped does it the other way.
//
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures True
func TwoClosersSwapped(a, b io.WriteCloser) {
	_, _ = fmt.Fprintf(b, "%d", 1)
	_, _ = io.WriteString(a, "a")
	_ = a.Close()
	_, _ = io.WriteString(b, "again")
	_ = b.Close()
}

// CloseTwice closes across an io.WriteString.
//
// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func CloseTwice(wc io.WriteCloser) {
	_ = wc.Close()
	_, _ = io.WriteString(wc, "x")
	_ = wc.Close() // want `precondition of wc.Close may not hold: ~closed\(c\)$`
}

// shut closes rc; its contract lists rc, so it may change the states of
// rc itself.
//
// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures True
func shut(rc io.ReadCloser) { _ = rc.Close() }

// ShutTwice closes after a call that may have closed: the message names no
// call, since shut changes the state of rc itself.
//
// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures True
func ShutTwice(rc io.ReadCloser) {
	shut(rc)
	_ = rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\)$`
}

// The values that are kept: the state of what they keep is not known after
// a call through them (following the kept writer into the result is not
// built; see the roadmap).

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func BufferedThenClose(wc io.WriteCloser) (err error) {
	bw := bufio.NewWriter(wc)
	_, _ = bw.WriteString("x")
	_ = bw.Flush()
	return wc.Close() // want `precondition of wc.Close may not hold: ~closed\(c\); the state may have been changed by bw.WriteString at io.go:\d+:\d+, which writes through what it is handed or what a value it is handed keeps`
}

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func LoggedThenClose(wc io.WriteCloser) (err error) {
	l := log.New(wc, "", 0)
	l.Printf("x")
	return wc.Close() // want `precondition of wc.Close may not hold: ~closed\(c\); the state may have been changed by l.Printf at io.go:\d+:\d+`
}

// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures True
func ScannedThenClose(rc io.ReadCloser) (err error) {
	sc := bufio.NewScanner(rc)
	_ = sc.Scan()
	return rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\); the state may have been changed by sc.Scan at io.go:\d+:\d+`
}

// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures True
func LimitedThenClose(rc io.ReadCloser) (err error) {
	_, _ = io.LimitReader(rc, 10).Read(make([]byte, 4))
	return rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\); the state may have been changed by io.LimitReader\(rc, 10\).Read at io.go:\d+:\d+`
}

// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures True
func MultiThenClose(a, b io.WriteCloser) {
	_, _ = io.MultiWriter(a, b).Write([]byte("x"))
	_ = a.Close() // want `precondition of a.Close may not hold: ~closed\(c\); the state may have been changed by io.MultiWriter\(a, b\).Write at io.go:\d+:\d+`
	_ = b.Close() // want `precondition of b.Close may not hold: ~closed\(c\); the state may have been changed by io.MultiWriter\(a, b\).Write at io.go:\d+:\d+`
}

// closeAll is trusted; its entry claims behind(wc) of an io.WriteCloser,
// whose Close changes a state, which the entry cannot claim.
func closeAll(wc io.WriteCloser) { wc.Close() }

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func UsesCloseAll(wc io.WriteCloser) {
	closeAll(wc) // want `the trusted contract of optionalio.closeAll \(trusted.yaml:\d+\) cannot be used: .*behind\(wc\) claims that the function changes no state of what wc holds, and io.WriteCloser has states`
}

// Interfaces without states that reach values with states (F22 of the
// review of S2 of F35): an entry over them cannot claim behind, since runs
// lets the function call what it reaches.

// Handing is written to and hands out a closer.
type Handing interface {
	io.Writer
	// @Ensures True
	Closer() (c io.Closer)
}

// HandingCloser is a Handing that is also closed.
type HandingCloser interface {
	Handing
	io.Closer
}

// flushAll is trusted: it closes what Closer returns.
func flushAll(p Handing) {
	if c := p.Closer(); c != nil {
		_ = c.Close()
	}
}

// @Requires x != nil And ~closed(x)
// @Modifies x
// @Ensures True
func UsesFlushAll(x HandingCloser) (err error) {
	flushAll(x) // want `the trusted contract of optionalio.flushAll \(trusted.yaml:\d+\) cannot be used: in its modifies "behind\(p\)": behind\(p\) claims that the function changes no state of what p holds, and what p holds reaches io.Closer, whose method Close it may call, a method of an interface with states; list p itself`
	return x.Close()
}

// Hooked is written to and hands out a function.
type Hooked interface {
	io.Writer
	// @Ensures True
	Hook() (f func())
}

// runHook is trusted: it calls the hook.
func runHook(p Hooked) {
	if f := p.Hook(); f != nil {
		f()
	}
}

// @Requires x != nil
// @Modifies x
// @Ensures True
func UsesRunHook(x Hooked) {
	runHook(x) // want `behind\(p\) claims that the function changes no state of what p holds, and what p holds reaches a function value of type func\(\), which it may call; list p itself`
}

// Filed is written to and hands out a file.
type Filed interface {
	io.Writer
	// @Ensures True
	File() (f *os.File)
}

// closeFile is trusted: it closes the file.
func closeFile(p Filed) {
	if f := p.File(); f != nil {
		_ = f.Close()
	}
}

// @Requires x != nil
// @Modifies x
// @Ensures True
func UsesCloseFile(x Filed) {
	closeFile(x) // want `behind\(p\) claims that the function changes no state of what p holds, and what p holds reaches \*os.File, which has states; list p itself`
}

// Named is written to and has a name: what it reaches has no states.
type Named interface {
	io.Writer
	// @Ensures True
	Name() (s string)
}

// NamedCloser is a Named that is also closed.
type NamedCloser interface {
	Named
	io.Closer
}

// writeName is trusted: it writes the name.
func writeName(p Named) { _, _ = io.WriteString(p, p.Name()) }

// UsesWriteName closes after writeName, whose entry claims behind(p).
//
// @Requires x != nil And ~closed(x)
// @Modifies x
// @Ensures True
func UsesWriteName(x NamedCloser) (err error) {
	writeName(x)
	return x.Close()
}
