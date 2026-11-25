package guide

import (
	"bufio"
	"fmt"
	"io"
)

// The programs of the section "Wrappers of readers and writers".

// @Requires r != nil And limit >= 0
// @Modifies r
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

// ReadLines wraps the error of Err, which may be one the reader returned,
// whose origin nothing can make known (S0 of F35): it is refused.
//
// @Requires r != nil And limit >= 0
// @Modifies r
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
		return n, fmt.Errorf("read lines: %w", err) // want `cannot verify ReadLines: formatting err would run the methods of an error whose origin is not known`
	}
	return n, nil
}

// @Requires r != nil
// @Modifies r
// @Ensures True
func ReadAll(r io.Reader) {
	sc := bufio.NewScanner(r)
	for sc.Scan() { // want `vego: loop needs a // @Variant annotation to prove that it terminates` `vego: precondition of Scan may not hold: ready\(s\)`
	}
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func WriteBuffered(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	if _, err = bw.Write([]byte("done\n")); err != nil {
		return err
	}
	return bw.Flush()
}

// @Requires w != nil
// @Ensures True
func WriteBufferedUnlisted(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	_, err = bw.Write([]byte("done\n")) // want `vego: Write may modify bw, which WriteBufferedUnlisted may not modify; it is memory that NewWriter returned, which its contract places in the footprint of w when it is not new; list w in a // @Modifies clause`
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
// @Modifies r, log
// @Ensures True
func ReadLogged(r io.Reader, log io.Writer) (err error) {
	rc := io.NopCloser(io.TeeReader(r, log))
	defer rc.Close()
	_, err = rc.Read(make([]byte, 512))
	return err
}

// @Requires header != nil And body != nil
// @Modifies header, body
// @Ensures True
func ReadParts(header, body io.Reader) (err error) {
	all := io.MultiReader(header, body)
	_, err = all.Read(make([]byte, 512))
	return err
}

// @Requires Forall i in [0, |parts|) : parts[i] != nil
// @Ensures True
func ReadAllParts(parts []io.Reader) (err error) {
	all := io.MultiReader(parts...)
	_, err = all.Read(make([]byte, 512)) // want `all.Read may modify the footprint of all, which ReadAllParts may not modify; it is a value that MultiReader returned at wrappers.go:\d+:\d+, and its contract places its footprint in those of what parts holds, which no // @Modifies clause can list yet; pass the values written out, one argument each, and list each of them`
	return err
}

// @Requires w != nil And 0 <= n <= 1000
// @Modifies w
// @Ensures True
func WriteCount(w io.Writer, n int) (err error) {
	bw := bufio.NewWriter(w)
	if _, err = fmt.Fprintf(bw, "%d items\n", n); err != nil {
		return err
	}
	return bw.Flush()
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func WriterAsWriter(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	var x io.Writer = bw // want `vego: cannot verify WriterAsWriter: converting a value of type \*bufio.Writer to io.Writer is not supported yet: its Write calls through the writer it keeps, and nothing proves yet that calls through values that wrap values end; pass the Writer itself to fmt.Fprintf, Fprint, or Fprintln, which then calls its own Write, or format into a string, as with fmt.Sprintf, and pass it to the Writer's own Write as \[\]byte\(s\)`
	_, err = x.Write([]byte("x"))
	return err
}

// @Requires w != nil And 0 <= n <= 1000
// @Modifies w
// @Ensures True
func WriteCountFormatted(w io.Writer, n int) (err error) {
	bw := bufio.NewWriter(w)
	s := fmt.Sprintf("%d items\n", n)
	if _, err = bw.Write([]byte(s)); err != nil {
		return err
	}
	return bw.Flush()
}

// CopySome copies from src to dst in at most 1000 reads of 4096 bytes.
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
