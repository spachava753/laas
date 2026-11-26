// Package sizes holds ordinary programs that append, concatenate, format,
// and write to buffers, with contracts that say what each is for and no
// clause about how long anything may be. Its trust file declares the
// memory of the machines (F38); nosizes holds the same programs without
// the declaration.
package sizes

import (
	"bytes"
	"errors"
	"fmt"
	"path/filepath"
	"strconv"
	"strings"
)

// @Modifies s
// @Ensures |r| = |s| + 1
func Push(s []int, x int) (r []int) {
	r = append(s, x)
	return r
}

// @Ensures |out| = |xs|
func Collect(xs []string) (out []string) {
	// @Invariant 0 <= i <= |xs| And |out| = i
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		out = append(out, xs[i])
	}
	return out
}

// @Ensures |r| = |a| + |b|
func Cat(a, b string) (r string) {
	r = a + b
	return r
}

// @Ensures |r| = |a| + 1 + |b|
func Pair(a, b string) (r string) {
	r = a + "=" + b
	return r
}

var errMissing = errors.New("missing")

// @Ensures found -> err = nil
func Wrap(name string, found bool) (err error) {
	if !found {
		return fmt.Errorf("reading %s: %w", name, errMissing)
	}
	return nil
}

// @Ensures ok -> err = nil
func NewError(text string, ok bool) (err error) {
	if !ok {
		return errors.New(text)
	}
	return nil
}

// @Ensures True
func Lower(s string) (r string) {
	r = strings.ToLower(s)
	return r
}

// @Ensures True
func Words(s string) (r []string) {
	r = strings.Split(s, ",")
	return r
}

// @Ensures True
func Label(n int) (r string) {
	r = strconv.Itoa(n) + "x"
	return r
}

// @Ensures True
func Setting(name string, n int) (r string) {
	r = fmt.Sprintf("%s=%d", name, n)
	return r
}

// @Ensures True
func Path(dir, name string) (r string) {
	r = filepath.Join(dir, name)
	return r
}

// @Ensures |r| = |xs|
func Copies(xs []string) (r []string) {
	r = make([]string, len(xs))
	return r
}

// @Ensures True
func Lines(xs []string) (r string) {
	var b strings.Builder
	// @Invariant 0 <= i <= |xs|
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		b.WriteString(xs[i])
		b.WriteByte('\n')
	}
	r = b.String()
	return r
}

// @Ensures True
func Table(names []string, n int) (r []byte) {
	var b bytes.Buffer
	// @Invariant 0 <= i <= |names|
	// @Variant |names| - i
	for i := 0; i < len(names); i++ {
		fmt.Fprintf(&b, "%s\t%d\n", names[i], n)
	}
	r = b.Bytes()
	return r
}

// Each calls the others with nothing to meet at the call.
// @Ensures True
func Report(xs []string, name string) (r string) {
	r = Pair(Lines(Collect(xs)), Lower(name))
	return r
}

// Doubling a slice 64 times verifies here, and on any input that is not
// empty it runs out of memory, which no proof covers: under the declared
// memory, growth that the program makes itself is no longer checked, only
// what is reserved by a number (F4 of the design review of F38).
// @Modifies s
// @Ensures True
func Doubles(s []byte) (r []byte) {
	r = s
	// @Invariant 0 <= i <= 64
	// @Variant 64 - i
	for i := 0; i < 64; i++ {
		r = append(r, r...)
	}
	return r
}

// A string is at most the memory itself, so the same bound on a string
// holds (F19 of the review of step 2a).
// @Requires 300 * |s| + 65536 <= MaxAlloc
// @Ensures True
func BigText(s string) (r string) {
	r = s
	return r
}

// @Ensures True
func HandsBigText(s string) (r string) {
	r = BigText(s)
	return r
}

// A reservation that the declaration allows.
// @Requires 0 <= n And n <= 1000
// @Ensures True
func GrowsBuilder(n int) (r string) {
	var b strings.Builder
	b.Grow(n)
	r = b.String()
	return r
}
