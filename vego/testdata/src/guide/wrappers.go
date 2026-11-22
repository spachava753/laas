package guide

import (
	"bufio"
	"fmt"
	"io"
)

// The programs of the section "Wrappers of readers and writers".

// @Requires r != nil And limit >= 0
// @Ensures 0 <= n And n <= limit
func PrintLines(r io.Reader, limit int) (n int, err error) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= n And n <= limit And ready(sc)
	// @Variant limit - n
	for n < limit && sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	return n, sc.Err()
}

// ReadLines verifies under the entry of the tests for (*bufio.Scanner).Err
// that the guide shows; under the shipped entries it is refused, as in
// the module scanerrs.
//
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

// @Requires bw != nil And ready(bw) And |p| > 0
// @Modifies bw
// @Ensures r = p[0]
func WriteThenRead(bw *bufio.Writer, p []byte) (r byte) {
	_ = bw.WriteByte('x')
	return p[0] // want `vego: postcondition may not hold: r = p\[0\]`
}

// @Requires r != nil And log != nil
// @Ensures True
func ReadLogged(r io.Reader, log io.Writer) (err error) {
	rc := io.NopCloser(io.TeeReader(r, log))
	defer rc.Close()
	_, err = rc.Read(make([]byte, 512))
	return err
}

// @Requires Forall i in [0, |parts|) : parts[i] != nil
// @Ensures True
func ReadParts(parts []io.Reader) (err error) {
	all := io.MultiReader(parts...)
	_, err = all.Read(make([]byte, 512))
	return err
}
