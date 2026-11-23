package footprints

import (
	"bufio"
	"fmt"
	"io"
	"log"
	"os"
)

// CopyOnce writes to w and then closes rc, which it was given open. The
// write may have closed rc, as a ResponseWriter may close the body of the
// request it answers: nothing keeps the states of rc outside what w
// writes (F14 of the design review).
//
// @Requires w != nil And rc != nil And ~closed(rc)
// @Modifies w, rc
// @Ensures True
func CopyOnce(w io.Writer, rc io.ReadCloser) {
	_, _ = w.Write([]byte("x"))
	_ = rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\)`
}

// Relay reads from rc into buf, writes what it read to w, and closes rc,
// which the write may have closed.
//
// @Requires w != nil And rc != nil And ~closed(rc) And |buf| > 0
// @Modifies w, rc, buf
// @Ensures True
func Relay(w io.Writer, rc io.ReadCloser, buf []byte) {
	n, _ := rc.Read(buf)
	if 0 <= n && n <= len(buf) {
		_, _ = w.Write(buf[:n])
	}
	_ = rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\)`
}

// LogThenClose logs a line through a logger over w and then closes rc,
// which the logger's write through w may have closed, as with Relay (F36 of
// the review of step 4).
//
// @Requires w != nil And rc != nil And ~closed(rc)
// @Modifies w, rc
// @Ensures True
func LogThenClose(w io.Writer, rc io.ReadCloser) {
	l := log.New(w, "", 0)
	l.Println("x")
	_ = rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\)`
}

// LogsUnlisted prints through a logger it does not list.
//
// @Requires l != nil And ready(l)
// @Ensures True
func LogsUnlisted(l *log.Logger) {
	l.Println("x") // want `vego: Println may modify l, which LogsUnlisted may not modify; list it in a // @Modifies clause, as l`
}

// CloseFirst closes rc before it writes, which keeps what it needs.
//
// @Requires w != nil And rc != nil And ~closed(rc)
// @Modifies w, rc
// @Ensures True
func CloseFirst(w io.Writer, rc io.ReadCloser) {
	_ = rc.Close()
	_, _ = w.Write([]byte("x"))
}

// Usage writes to standard error, a file whose methods write nothing a
// caller can see, and lists nothing (E12).
//
// @Ensures True
func Usage() {
	fmt.Fprintln(os.Stderr, "usage: tool [command]")
}

// CountStdin counts the lines of standard input (E13).
//
// @Ensures 0 <= n And n <= 1000
func CountStdin() (n int) {
	sc := bufio.NewScanner(os.Stdin)
	// @Invariant 0 <= n And n <= 1000 And ready(sc)
	// @Variant 1000 - n
	for n < 1000 && sc.Scan() {
		n++
	}
	return n
}

// LogsToStderr logs through a logger over standard error (E14).
//
// @Requires |name| <= 1000
// @Ensures True
func LogsToStderr(name string) {
	l := log.New(os.Stderr, "", 0)
	l.Printf("checked %s", name)
}

// Emit writes a line to w (E15).
//
// @Requires w != nil And |msg| <= 1000
// @Modifies w
// @Ensures True
func Emit(w io.Writer, msg string) {
	fmt.Fprintf(w, "%s\n", msg)
}

// ToStdout emits to standard output, which needs no Modifies.
//
// @Ensures True
func ToStdout() {
	Emit(os.Stdout, "hi")
}

// ToFile emits to a file it creates, which needs no Modifies.
//
// @Requires |path| <= 4096
// @Ensures True
func ToFile(path string) (err error) {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	Emit(f, "hi")
	return f.Close()
}

// ConvertsThenWrites writes to standard error, whose footprint is empty,
// and then through a writer it does not list.
//
// @Requires w != nil
// @Ensures True
func ConvertsThenWrites(w io.Writer) {
	fmt.Fprintln(os.Stderr, "start")
	_, _ = w.Write([]byte("x")) // want `w.Write may modify the footprint of w, which ConvertsThenWrites may not modify; list it in a // @Modifies clause`
}

// tally counts the writes to it in its own struct, up to a bound.
type tally struct{ n int }

// @Requires t != nil
// @Modifies t
// @Ensures n = |p| And err = nil
func (t *tally) Write(p []byte) (n int, err error) {
	if t.n < 1000000 {
		t.n++
	}
	return len(p), nil
}

// CountsThenFormats formats into a counter converted to an io.Writer,
// whose footprint is the struct t points to.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func CountsThenFormats(t *tally) {
	fmt.Fprintln(t, "x")
}

// CountsUnlisted is CountsThenFormats without t listed.
//
// @Requires t != nil
// @Ensures True
func CountsUnlisted(t *tally) {
	fmt.Fprintln(t, "x") // want `vego: Fprintln may modify the footprint of t, which CountsUnlisted may not modify; it is the memory that t points to, converted at d1.go:\d+:\d+; list t in a // @Modifies clause`
}

// boundedTally has a Write whose precondition io.Writer's Write does not
// give it.
type boundedTally struct{ n int }

// @Requires t != nil And t.n < MaxInt - |p|
// @Modifies t
// @Ensures n = |p| And err = nil
func (t *boundedTally) Write(p []byte) (n int, err error) {
	t.n += len(p)
	return len(p), nil
}

// FormatsBounded converts a boundedTally to an io.Writer, which its Write
// cannot meet.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func FormatsBounded(t *boundedTally) {
	fmt.Fprintln(t, "x") // want `vego: precondition of Write may not hold: t.n < MaxInt - \|p\|, in \(\*boundedTally\).Write used as a method of io.Writer`
}

// storesInto is trusted to write b, which may store into it a reference of
// any origin, and to return a new pair.
func storesInto(b *Box) (p *Pair) { return &Pair{} }

// PollutesInArgument hands Touch a pair that a call made in its arguments
// returned, after that call may have stored into b what s writes.
//
// @Requires s != nil And b != nil
// @Modifies s, b
// @Ensures True
func PollutesInArgument(s Sink, b *Box) {
	Touch(s, storesInto(b)) // want `the footprint of what is passed to Touch as s may hold memory that what is passed as storesInto\(b\) reaches, and Touch relies on it not doing so: the call of storesInto at d1.go:\d+:\d+ may store into memory it may modify a reference to memory of any origin`
}

// KeepsMaybe writes through s when it is not nil, and keeps what q points
// to.
//
// @Requires q != nil
// @Modifies s
// @Ensures q.A' = q.A
func KeepsMaybe(s Sink, q *Pair) {
	if s != nil {
		_ = s.Put(nil)
	}
}

// PassesNil hands KeepsMaybe no writer. A nil value writes nothing, but the
// proof of separation asks that the argument be a parameter whose footprint
// the caller lists, so it is refused (Not built in the roadmap).
//
// @Requires q != nil
// @Ensures True
func PassesNil(q *Pair) {
	KeepsMaybe(nil, q) // want `the footprint of what is passed to KeepsMaybe as nil may hold memory that what is passed as q reaches, and KeepsMaybe relies on it not doing so: nil is not a parameter whose footprint PassesNil's own Modifies lists, or a value made from such parameters by a call whose contract says so with fresh\(result, w\), so nothing places it`
}
