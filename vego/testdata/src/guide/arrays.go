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
	total  int
}

// @Requires h != nil And h.counts[b] < 1000000 And h.total < 1000000
// @Modifies h
// @Ensures h.counts'[b] = h.counts[b] + 1 And h.total' = h.total + 1
// @Ensures Forall k in [0, 256) : k != b -> h.counts'[k] = h.counts[k]
func (h *histogram) Count(b byte) {
	h.counts[b]++
	h.total++
}

type names struct {
	list [2]string
}

// @Requires n != nil
// @Ensures True
func (n *names) First() (r string) { // want `cannot verify First: parameter n has unsupported type \*guide.names; guide.names holds an array of string in field list, and arrays in structs are supported only for elements that are numbers or booleans yet`
	return n.list[0]
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

// reverse gives the value of a decimal digit, and 0 for any other byte.
var reverse = [256]byte{
	'0': 0, '1': 1, '2': 2, '3': 3, '4': 4, '5': 5, '6': 6, '7': 7, '8': 8, '9': 9,
}

// @Requires '0' <= c <= '9'
// @Ensures r = c - 48
func DigitValue(c byte) (r byte) {
	return reverse[c]
}

type block struct {
	n    int
	word [4]uint32
}

// @Requires b != nil
// @Modifies b.word
// @Ensures b.word'[2] = 7 And b.word'[1] = b.word[1] And b.n' = b.n
func (b *block) setWord() {
	p := &b.word
	p[2] = 7
}

// @Requires p != nil
// @Ensures True
func clearWords(p *[4]uint32) { // want `cannot verify clearWords: parameter p has type \*\[4\]uint32, a pointer to an array, and pointers to arrays are supported only in local variables yet; pass or keep a slice of the array, as in p\[:\]`
	*p = [4]uint32{}
}
