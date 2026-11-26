package nosizes

import (
	"bytes"
	"fmt"
	"io"
)

// @Requires w != nil
// @Modifies w
// @Ensures True
func emit(w io.Writer, s string) (err error) {
	_, err = io.WriteString(w, s)
	return err
}

// Without a declared memory a buffer is not converted, and the message
// says what would allow it (step 3b of F38).
// @Ensures True
func Emitted(s string) (r string, err error) {
	var b bytes.Buffer
	err = emit(&b, s) // want `vego: cannot verify Emitted: converting a value of type \*bytes.Buffer to io.Writer is not supported: its Write may panic when the buffer is too large to grow, and the contract of \(io.Writer\).Write has no bound for it; declare the memory of the machines the program runs on under sizes in vego-trusted.yaml, under which a buffer converts`
	r = b.String()
	return r, err
}

// Formatting into a buffer keeps its own route, and the bound on what it
// writes, as with the declaration (sizes.Formatted).
// @Requires 0 <= n And n <= 1000
// @Ensures |r| <= 10000
func Formatted(n int) (r string) {
	var b bytes.Buffer
	fmt.Fprintf(&b, "%d items", n)
	r = b.String()
	return r
}
