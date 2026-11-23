package buffers

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
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
