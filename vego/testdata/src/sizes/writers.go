package sizes

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"log"
	"strings"
)

// Under the declared memory a *bytes.Buffer and a *strings.Builder convert
// to io.Writer with what they own, as an owner of the project does (step 3b
// of F38). What a caller knows of the buffer after a callee wrote through
// the interface value is what holds of every buffer: its length is not
// known (sizesbad.LengthAfter).

// @Requires w != nil
// @Modifies w
// @Ensures True
func emit(w io.Writer, s string) (err error) {
	_, err = io.WriteString(w, s)
	return err
}

// @Ensures True
func Emitted(s string) (r string, err error) {
	var b bytes.Buffer
	err = emit(&b, s)
	r = b.String()
	return r, err
}

// @Ensures True
func EmittedToBuilder(s string) (r string, err error) {
	var b strings.Builder
	err = emit(&b, s)
	r = b.String()
	return r, err
}

// @Requires x != nil And y != nil
// @Modifies x, y
// @Ensures True
func both(x, y io.Writer) (err error) {
	if err = emit(x, "a"); err != nil {
		return err
	}
	return emit(y, "b")
}

// Two buffers through one helper, in both orders.
// @Ensures True
func Two() (r string, err error) {
	var x, y bytes.Buffer
	if err = both(&x, &y); err != nil {
		return "", err
	}
	if err = both(&y, &x); err != nil {
		return "", err
	}
	r = x.String() + y.String()
	return r, err
}

// @Ensures True
func Flushed(s string) (r string, err error) {
	var b strings.Builder
	w := bufio.NewWriter(&b)
	if _, err = w.WriteString(s); err != nil {
		return "", err
	}
	err = w.Flush()
	r = b.String()
	return r, err
}

// @Ensures True
func Logged(n int) (r string) {
	var b bytes.Buffer
	l := log.New(&b, "", 0)
	l.Printf("n=%d", n)
	r = b.String()
	return r
}

// Formatting into a buffer keeps its own route, and the bound on what it
// writes, as without the declaration (nosizes.Formatted).
// @Requires 0 <= n And n <= 1000
// @Ensures |r| <= 10000
func Formatted(n int) (r string) {
	var b bytes.Buffer
	fmt.Fprintf(&b, "%d items", n)
	r = b.String()
	return r
}
