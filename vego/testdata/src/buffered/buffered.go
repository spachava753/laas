// Package buffered uses the shipped entries of bufio: a Scanner over a
// reader it is given, and a Reader and a Writer that it is handed.
package buffered

import (
	"bufio"
	"fmt"
	"io"
)

// CountLines counts at most limit lines of r.
//
// @Requires r != nil And limit >= 0
// @Ensures 0 <= n And n <= limit
func CountLines(r io.Reader, limit int) (n int, err error) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= n And n <= limit And ready(sc)
	// @Variant limit - n
	for n < limit && sc.Scan() {
		n++
	}
	return n, sc.Err()
}

// LongestLine returns the length of the longest of at most limit lines.
//
// @Requires r != nil And limit >= 0
// @Ensures 0 <= longest And longest <= 65536
func LongestLine(r io.Reader, limit int) (longest int) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= i And i <= limit And ready(sc) And 0 <= longest And longest <= 65536
	// @Variant limit - i
	for i := 0; i < limit && sc.Scan(); i++ {
		if line := sc.Text(); len(line) > longest {
			longest = len(line)
		}
	}
	return longest
}

// PrintLines prints at most limit lines of r, which a line's bound lets
// fmt format.
//
// @Requires r != nil And limit >= 0
// @Ensures True
func PrintLines(r io.Reader, limit int) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= i And i <= limit And ready(sc)
	// @Variant limit - i
	for i := 0; i < limit && sc.Scan(); i++ {
		fmt.Println(sc.Text())
	}
}

// ScansForEver reads until the input ends, which an endless reader never
// does.
//
// @Requires r != nil
// @Ensures True
func ScansForEver(r io.Reader) (n int) {
	sc := bufio.NewScanner(r)
	for sc.Scan() { // want `vego: loop needs a .*Variant annotation to prove that it terminates` `vego: precondition of Scan may not hold: ready\(s\)`
	}
	return 0
}

// ScansWithoutInvariant forgets in the loop that the Scanner is ready.
//
// @Requires r != nil And limit >= 0
// @Ensures True
func ScansWithoutInvariant(r io.Reader, limit int) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= i And i <= limit
	// @Variant limit - i
	for i := 0; i < limit && sc.Scan(); i++ { // want `vego: precondition of Scan may not hold: ready\(s\)`
	}
}

// ScansGiven scans a Scanner it is handed, of which nothing says that it
// is ready: code that is not verified may have called Split on it.
//
// @Requires sc != nil
// @Modifies sc
// @Ensures True
func ScansGiven(sc *bufio.Scanner) (more bool) {
	return sc.Scan() // want `vego: precondition of Scan may not hold: ready\(s\)`
}

// ScansReady scans a Scanner it is handed that is ready.
//
// @Requires sc != nil And ready(sc)
// @Modifies sc
// @Ensures ready(sc')
func ScansReady(sc *bufio.Scanner) (more bool) {
	return sc.Scan()
}

// ScansNil makes a Scanner over no reader.
//
// @Ensures True
func ScansNil() {
	_ = bufio.NewScanner(nil) // want `vego: precondition of NewScanner may not hold: r != nil`
}

// ScansZero scans a Scanner made as a zero value.
//
// @Ensures True
func ScansZero() (more bool) {
	sc := &bufio.Scanner{}
	return sc.Scan() // want `vego: precondition of Scan may not hold: ready\(s\)`
}

// WrapsErr wraps the error of a Scanner, which the entry of the tests for
// (*bufio.Scanner).Err vouches for; the module scanerrs, which has no such
// entry, cannot.
//
// @Requires r != nil
// @Ensures True
func WrapsErr(r io.Reader) (err error) {
	sc := bufio.NewScanner(r)
	if err := sc.Err(); err != nil {
		return fmt.Errorf("scan: %w", err)
	}
	return nil
}

// FirstByte reads a byte from a Reader it is handed.
//
// @Requires br != nil And ready(br)
// @Modifies br
// @Ensures ready(br')
func FirstByte(br *bufio.Reader) (c byte, err error) {
	return br.ReadByte()
}

// Report writes a total to a Writer it is handed and flushes it.
//
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func Report(bw *bufio.Writer, total []byte) (err error) {
	if _, err = bw.Write(total); err != nil {
		return err
	}
	if err = bw.WriteByte('\n'); err != nil {
		return err
	}
	return bw.Flush()
}

// WritesLocally makes a Writer over w and writes to it. NewWriter may
// return the Writer that w holds, so the write may be to memory that
// existed when WritesLocally was called.
//
// @Requires w != nil
// @Ensures True
func WritesLocally(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	return bw.Flush() // want `vego: Flush may modify bw, which WritesLocally may not modify; it is memory that NewWriter returned, and its contract does not say that this is new memory, so it may have existed when WritesLocally was called; take it as a parameter and list it in a // @Modifies clause`
}

// MakesWriter makes a Writer for its caller to use.
//
// @Requires w != nil
// @Ensures bw != nil And ready(bw)
func MakesWriter(w io.Writer) (bw *bufio.Writer) {
	return bufio.NewWriter(w)
}

// ReadsReset reads from a Reader whose reader code that is not verified
// may have reset to nil.
//
// @Requires br != nil
// @Modifies br
// @Ensures True
func ReadsReset(br *bufio.Reader) {
	_, _ = br.ReadByte() // want `vego: precondition of ReadByte may not hold: ready\(b\)`
}
