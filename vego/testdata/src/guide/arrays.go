package guide

import (
	"crypto/sha256"
	"encoding/hex"
	"io"
)

// The programs of the section Arrays of docs/verification.md.

// Counts counts how often each byte value below 16 occurs.
//
// @Requires Forall k in [0, |data|) : data[k] < 16
// @Requires |data| <= 1000
// @Ensures Forall v in [0, 16) : 0 <= counts[v] <= |data|
func Counts(data []byte) (counts [16]int) {
	// @Invariant 0 <= i <= |data|
	// @Invariant Forall v in [0, 16) : 0 <= counts[v] <= i
	for i := range data {
		counts[data[i]]++
	}
	return counts
}

// @Ensures r = 1
func CopyIsAValue() (r int) {
	a := [3]int{1, 2, 3}
	b := a
	b[0] = 9
	return a[0]
}

// @Ensures r = 9
func CopyIsAValueWrong() (r int) {
	a := [3]int{1, 2, 3}
	b := a
	b[0] = 9
	return a[0] // want `postcondition may not hold: r = 9`
}

// @Requires r != nil
// @Modifies r
// @Ensures 0 <= n <= 512
func ReadBlock(r io.Reader) (n int, err error) {
	var buf [512]byte
	return r.Read(buf[:])
}

// @Ensures |result| = 64
func Fingerprint(data []byte) (result string) {
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:])
}

// @Ensures r = 5 And s = 4
func AppendIntoArray() (r byte, s int) {
	var buf [4]byte
	t := append(buf[:1], 5)
	return buf[1], cap(t)
}

// @Requires |p| >= 4
// @Ensures r[0] = p[0]
func Header(p []byte) (r [4]byte) {
	return [4]byte(p)
}

// @Ensures True
func HeaderShort(p []byte) (r [4]byte) {
	return [4]byte(p) // want `the conversion may panic: p may be shorter than \[4\]byte`
}

// @Ensures True
func Names() (r string) {
	names := [2]string{"a", "b"} // want `cannot verify Names: names has unsupported type \[2\]string; \[2\]string is an array of string, and only arrays of numbers and booleans are supported yet; use a slice of string instead`
	return names[0]
}

// line holds a buffer of bytes and how many of them are used.
type line struct {
	used int
	buf  [80]byte
}

// @Requires l != nil And 0 <= l.used < 80
// @Modifies l
// @Ensures l.used' = l.used + 1 And l.buf'[l.used] = c
func (l *line) Add(c byte) {
	l.buf[l.used] = c
	l.used++
}

// @Requires l != nil And |p| <= 80
// @Requires apart(p, l.buf)
// @Modifies l
// @Ensures Forall k in [0, |p|) : l.buf'[k] = p[k]
func (l *line) Load(p []byte) {
	// @Invariant 0 <= i <= |p|
	// @Invariant Forall k in [0, i) : l.buf[k] = p[k]
	for i := range p {
		l.buf[i] = p[i]
	}
}

// @Requires l != nil
// @Modifies l
// @Ensures True
func (l *line) Reload() {
	l.Load(l.buf[:8]) // want `precondition of Load may not hold: apart\(p, l.buf\)`
}

type histogram struct {
	counts [256]int
}

// @Requires h != nil
// @Ensures True
func (h *histogram) Total() (n int) { // want `cannot verify Total: parameter h has unsupported type \*guide.histogram; guide.histogram holds an array of int in field counts, and arrays in structs are supported only for elements of one byte yet`
	return 0
}

// @Requires 0 <= n <= |buf|
// @Modifies buf
// @Ensures r = |buf| - n
// @Ensures Forall k in [0, |buf| - n) : buf'[k] = buf[k + n]
func ShiftDown(buf []byte, n int) (r int) {
	return copy(buf, buf[n:])
}

// @Requires |buf| = 4
// @Modifies buf
// @Ensures buf'[3] = buf[0]
func ShiftUpWrong(buf []byte) {
	copy(buf[1:], buf)
} // want `postcondition may not hold: buf'\[3\] = buf\[0\]`

// @Ensures n = 5 And name[0] = 'h'
func Name() (name [16]byte, n int) {
	n = copy(name[:], "hello")
	return name, n
}
