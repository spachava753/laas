package guide

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"strings"
)

// The programs of the sections "Building text in a buffer" and
// "Formatting into a buffer".

// @Requires |parts| <= 1000 And (Forall i in [0, |parts|) : |parts[i]| <= 1000)
// @Ensures |r| <= 1001 * |parts|
func JoinWithCommas(parts []string) (r string) {
	var b strings.Builder
	// @Invariant 0 <= i And i <= |parts| And |b| <= 1001 * i
	// @Variant |parts| - i
	for i := 0; i < len(parts); i++ {
		b.WriteString(parts[i])
		b.WriteByte(',')
	}
	return b.String()
}

// @Ensures True
func JoinUnbounded(parts []string) (r string) {
	var b strings.Builder
	for _, s := range parts {
		b.WriteString(s) // want `vego: precondition of WriteString may not hold: 2 \* \(\|b\| \+ \|s\|\) \+ 65536 <= MaxAlloc; it holds when \|b\| <= 10000000000000 and \|s\| <= 10000000000000`
	}
	return b.String()
}

// @Requires b != nil And |b| <= 1000000 And |line| <= 1000
// @Modifies b
// @Ensures |b'| = |b| + |line| + 1
func AddLine(b *strings.Builder, line string) {
	b.WriteString(line)
	b.WriteByte('\n')
}

// @Ensures |r| = 6
func TwoLines() (r string) {
	var b strings.Builder
	AddLine(&b, "ab")
	AddLine(&b, "cd")
	return b.String()
}

// LineBook collects lines in a Builder it holds.
type LineBook struct {
	lines int
	text  strings.Builder
}

// @Requires r != nil And |r.text| <= 1000000 And |line| <= 1000 And r.lines < 1000000
// @Modifies r
// @Ensures |r.text'| = |r.text| + |line| + 1 And r.lines' = r.lines + 1
func (r *LineBook) Add(line string) {
	r.text.WriteString(line)
	r.text.WriteByte('\n')
	r.lines++
}

// @Ensures r
func Overwritten() (r bool) {
	var b bytes.Buffer
	b.WriteString("abc")
	p := b.Bytes()
	first := p[0]
	b.Reset()
	b.WriteByte('z')
	return p[0] == first // want `vego: postcondition may not hold: r`
}

// @Requires b != nil And |b| <= 1000000 And 0 <= n And n <= 1000
// @Modifies b
// @Ensures True
func WriteItems(b *bytes.Buffer, n int) {
	fmt.Fprintf(b, "%d items\n", n)
}

// @Requires b != nil And |b| <= 1000000
// @Modifies b
// @Ensures True
func WriteFailure(b *bytes.Buffer) {
	fmt.Fprintf(b, "failed: %v\n", errors.New("disk full")) // want `vego: Fprintf writes to b text whose length is not known: it formats the text of an error, what a String or Error method returns, or strings or slices inside an element of a slice, whose lengths are not counted, and the Write of \*bytes.Buffer needs a bound on what it is given; format only values whose length the bound counts`
}

// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func WriteFailureBuffered(bw *bufio.Writer) (err error) {
	_, err = fmt.Fprintf(bw, "failed: %v\n", errors.New("disk full"))
	return err
}

// @Requires b != nil And |b| <= 1000000 And 0 <= k And k <= 1000
// @Modifies b
// @Ensures True
func WriteNumbers(b *bytes.Buffer, k int) {
	// @Invariant 0 <= i And i <= k And |b| <= |old(b)| + 500 * i
	// @Variant k - i
	for i := 0; i < k; i++ {
		fmt.Fprintf(b, "%d,", i)
	}
}

// @Requires b != nil And |b| <= 1000000 And 0 <= k And k <= 1000
// @Modifies b
// @Ensures True
func WriteNumbersTight(b *bytes.Buffer, k int) {
	// @Invariant 0 <= i And i <= k And |b| <= |old(b)| + 21 * i
	// @Variant k - i
	for i := 0; i < k; i++ { // want `vego: loop invariant may not be preserved: \|b\| <= \|old\(b\)\| \+ 21 \* i`
		fmt.Fprintf(b, "%d,", i)
	}
}
