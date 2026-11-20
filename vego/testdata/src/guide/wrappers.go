package guide

import (
	"bufio"
	"fmt"
	"io"
)

// The programs of the section "Wrappers of readers and writers".

// @Requires r != nil And limit >= 0
// @Ensures 0 <= n And n <= limit
func ReadLines(r io.Reader, limit int) (n int, err error) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= n And n <= limit And ready(sc)
	// @Variant limit - n
	for n < limit && sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	if err := sc.Err(); err != nil {
		return n, fmt.Errorf("read lines: %w", err)
	}
	return n, nil
}

// @Requires r != nil
// @Ensures True
func ReadAll(r io.Reader) {
	sc := bufio.NewScanner(r)
	for sc.Scan() { // want `vego: loop needs a // @Variant annotation to prove that it terminates` `vego: precondition of Scan may not hold: ready\(s\)`
	}
}

// @Requires w != nil
// @Ensures True
func WriteBuffered(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	_, err = bw.Write([]byte("done\n")) // want `vego: Write may modify bw, which WriteBuffered may not modify; it is memory that NewWriter returned, and its contract does not say that this is new memory, so it may have existed when WriteBuffered was called; take it as a parameter and list it in a // @Modifies clause`
	return err
}

// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func WriteTotal(bw *bufio.Writer, total []byte) (err error) {
	if _, err = bw.Write(total); err != nil {
		return err
	}
	return bw.Flush()
}
