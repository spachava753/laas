// Package noinputs is the corpus of inputs without the declaration that
// inputs end: nothing is known of a reader's end, and ends and unread are
// no words of the language (F39, part B).
package noinputs

import (
	"bufio"
	"fmt"
	"io"
	"os"
)

// CountLines counts the lines of standard input with the measure of the
// declaration, which is not there.
//
// @Ensures n >= 0
func CountLines() (n int) {
	sc := bufio.NewScanner(os.Stdin)
	// @Invariant ready(sc) And 0 <= n
	// @Variant unread(sc) // want `in Variant annotation: unread\(sc\) speaks of a reader that ends, which is known only where the trust file declares that inputs end; declare inputs in vego-trusted.yaml, or bound the number of reads`
	for sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	return n
}

// Drain requires that its reader ends.
//
// @Requires r != nil And ends(r) // want `ends\(r\) speaks of a reader that ends`
// @Modifies r
// @Ensures True
func Drain(r io.Reader) {
	_, _ = r.Read(make([]byte, 1))
}

// Words keeps a field and a variable named as the words are.
type Words struct {
	unread int
	ends   bool
}

// Fields reads them.
//
// @Requires w != nil
// @Ensures r = w.unread
func Fields(w *Words) (r int) {
	ends := w.ends
	if ends {
		return w.unread
	}
	return w.unread
}
