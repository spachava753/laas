package buffers

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
	"plog"
	"strings"
)

// Items formats into a Builder: Sprintf, then the Builder's own Write.
//
// @Requires 0 <= n And n <= 1000
// @Ensures |r| <= 10000
func Items(n int) (r string) {
	var b strings.Builder
	fmt.Fprintf(&b, "%d items", n)
	return b.String()
}

// ItemsBuffer formats into a Buffer it is handed, which it lists.
//
// @Requires b != nil And |b| <= 1000000 And |name| <= 1000
// @Modifies b
// @Ensures |b'| <= |b| + 10000 + 6 * |name|
func ItemsBuffer(b *bytes.Buffer, name string) {
	fmt.Fprintf(b, "%q\n", name)
}

// ItemsBufferUnbounded formats into a Buffer with no bound on its length.
//
// @Requires b != nil And |name| <= 1000
// @Modifies b
// @Ensures True
func ItemsBufferUnbounded(b *bytes.Buffer, name string) {
	fmt.Fprintf(b, "%q\n", name) // want `precondition of Write may not hold: 3 \* \(\|b\| \+ \|p\|\) \+ 65536 <= MaxAlloc; it holds when \|b\| <= [0-9]+ and \|\[\]byte\(Sprintf\(...\)\)\| <= [0-9]+`
}

// ItemsUnlisted formats into a Buffer it does not list.
//
// @Requires b != nil And |b| <= 1000000
// @Ensures True
func ItemsUnlisted(b *bytes.Buffer) {
	fmt.Fprint(b, 7) // want `Write may modify b, which ItemsUnlisted may not modify`
}

// NilBuffer formats into a nil Buffer, which converted would be an
// io.Writer that is not nil, and whose own Write panics.
//
// @Ensures True
func NilBuffer() {
	var b *bytes.Buffer
	fmt.Fprintln(b, "x") // want `precondition of Write may not hold: b != nil`
}

// FormatsError formats an error into a Buffer: the length of its text is
// not known, so neither is how long the buffer grows.
//
// @Ensures True
func FormatsError() {
	var b bytes.Buffer
	err := errors.New("x")
	fmt.Fprintf(&b, "%v", err) // want `Fprintf writes to &b text whose length is not known: it formats the text of an error`
}

// ToWriter formats into a bufio.Writer, whose Write calls through the
// writer it keeps: the Sprintf, then the Writer's own Write.
//
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures ready(bw')
func ToWriter(bw *bufio.Writer, n int) (err error) {
	_, err = fmt.Fprintf(bw, "%d\n", n)
	return err
}

// ToWriterNotReady formats into a bufio.Writer that may not be ready.
//
// @Requires bw != nil
// @Modifies bw
// @Ensures True
func ToWriterNotReady(bw *bufio.Writer, n int) (err error) {
	_, err = fmt.Fprintf(bw, "%d\n", n) // want `precondition of Write may not hold: ready\(b\)`
	return err
}

// Results returns what Fprint returns, which is what the Builder's Write
// returns: the number of bytes written, which is how much the Builder grew.
//
// @Ensures n = m And err = nil
func Results() (n, m int, err error) {
	var b strings.Builder
	n, err = fmt.Fprint(&b, "abc")
	return n, b.Len(), err
}

// ConvertsBuffer converts a Buffer to an io.Writer outside a call of a
// function that prints, which stays refused.
//
// @Ensures True
func ConvertsBuffer() {
	var b bytes.Buffer
	var w io.Writer = &b // want `converting a value of type \*bytes.Buffer to io.Writer is not supported: its Write may panic when the buffer is too large to grow`
	_ = w
}

// ErrToBufio formats an error into a bufio.Writer, whose Write needs no
// bound on what it is given, under the assumption about the text of an
// error that formatting makes everywhere.
//
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func ErrToBufio(bw *bufio.Writer) (err error) {
	e := errors.New("x")
	_, err = fmt.Fprintf(bw, "error: %v\n", e)
	return err
}

// Deferred formats into a Builder in a deferred call, which runs at the
// return as the Sprint function and the Builder's own Write.
//
// @Ensures True
func Deferred() {
	var b strings.Builder
	defer fmt.Fprintf(&b, "%d", 7)
	b.WriteByte('x')
}

// ProjectPrints formats into a Builder through a project function whose
// entry claims prints.
//
// @Ensures True
func ProjectPrints() {
	var b strings.Builder
	plog.Fprintf(&b, "%d items", 3)
}

// ProjectRequires formats through a project function whose entry claims
// prints and requires more than a writer, which the route would not check:
// the entry is refused.
//
// @Ensures True
func ProjectRequires() {
	var b strings.Builder
	plog.Checked(&b, "0123456789abcdef") // want `prints is claimed only of a function whose requires is w != nil`
}

// ProjectModifies formats through a project function whose entry claims
// prints and lists more than its writer: the entry is refused.
//
// @Ensures True
func ProjectModifies() {
	var b strings.Builder
	plog.Counted(&b, "x") // want `prints is claimed only of a function that writes nothing but through its writer`
}

// LoopInto formats into a Buffer it is handed, in a loop: the loop writes
// what the Buffer's own Write writes, which Modifies b covers.
//
// @Requires b != nil And |b| <= 1000000 And 0 <= k And k <= 1000
// @Modifies b
// @Ensures True
func LoopInto(b *bytes.Buffer, k int) {
	// @Invariant 0 <= i And i <= k And |b| <= |old(b)| + 10000 * i
	// @Variant k - i
	for i := 0; i < k; i++ {
		fmt.Fprintf(b, "%d\n", i)
	}
}

// LoopKeepsBytes claims that formatting into a Buffer in a loop keeps what
// Bytes returned before it. A Buffer that has been read slides its unread
// bytes to the front when a write does not fit after them, so it may not.
//
// @Requires b != nil And 0 < |b| And |b| <= 1000 And 0 <= k And k <= 10
// @Modifies b
// @Ensures r
func LoopKeepsBytes(b *bytes.Buffer, k int) (r bool) {
	p := b.Bytes()
	first := p[0]
	// @Invariant 0 <= i And i <= k And |b| <= |old(b)| + 10000 * i
	// @Variant k - i
	for i := 0; i < k; i++ {
		fmt.Fprint(b, "x")
	}
	return p[0] == first // want `postcondition may not hold: r`
}
