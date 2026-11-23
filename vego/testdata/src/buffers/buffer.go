package buffers

import "bytes"

// Lines writes each line and a newline to a Buffer.
//
// @Requires |lines| <= 1000 And (Forall i in [0, |lines|) : |lines[i]| <= 1000)
// @Ensures |r| <= 1001 * |lines|
func Lines(lines []string) (r []byte) {
	var b bytes.Buffer
	// @Invariant 0 <= i And i <= |lines| And |b| <= 1001 * i
	// @Variant |lines| - i
	for i := 0; i < len(lines); i++ {
		b.WriteString(lines[i])
		b.WriteByte('\n')
	}
	return b.Bytes()
}

// Record appends s to b and a newline, under a bound a caller can prove.
//
// @Requires b != nil And |b| <= 1000000 And |s| <= 1000
// @Modifies b
// @Ensures |b'| = |b| + |s| + 1
func Record(b *bytes.Buffer, s string) {
	b.WriteString(s)
	b.WriteByte('\n')
}

// RecordUnbounded writes s with no bound on b.
//
// @Requires b != nil And |s| <= 1000
// @Modifies b
// @Ensures True
func RecordUnbounded(b *bytes.Buffer, s string) {
	b.WriteString(s) // want `precondition of WriteString may not hold: 3 \* \(\|b\| \+ \|s\|\) \+ 65536 <= MaxAlloc; it holds when \|b\| <= [0-9]+ and \|s\| <= [0-9]+`
}

// Sizes uses every method that keeps or sets the length.
//
// @Requires 0 <= k And k <= 100
// @Ensures n = 3
func Sizes(k int) (n int) {
	var b bytes.Buffer
	b.Grow(k)
	b.Write([]byte("abcd"))
	b.WriteRune('é')
	b.Truncate(2)
	b.WriteByte('z')
	s := b.String()
	return len(s)
}

// TruncatePast truncates past the length, which panics.
//
// @Ensures True
func TruncatePast() {
	var b bytes.Buffer
	b.WriteString("ab")
	b.Truncate(3) // want `precondition of Truncate may not hold: n <= \|b\|`
}

// ResetEmpties writes, resets, and reads the length.
//
// @Ensures n = 0
func ResetEmpties() (n int) {
	var b bytes.Buffer
	b.WriteString("abc")
	b.Reset()
	return b.Len()
}

// BytesKept reads a byte of what Bytes returned with no write in between.
//
// @Ensures r
func BytesKept() (r bool) {
	var b bytes.Buffer
	b.WriteString("abc")
	p := b.Bytes()
	first := p[0]
	return p[0] == first
}

// BytesOverwritten is the reviewer's program of part 1 without the
// interface value: Truncate keeps the array, so the write may put z where
// p[0] is.
//
// @Ensures r
func BytesOverwritten() (r bool) {
	var b bytes.Buffer
	b.WriteString("abc")
	p := b.Bytes()
	first := p[0]
	b.Truncate(0)
	b.WriteByte('z')
	return p[0] == first // want `postcondition may not hold: r`
}

// WritesOwnBytes writes a buffer's own unread bytes to it, on a buffer
// that may have been read from: only the length is known after it.
//
// @Requires b != nil And |b| <= 1000
// @Modifies b
// @Ensures |b'| = 2 * |b|
func WritesOwnBytes(b *bytes.Buffer) {
	b.Write(b.Bytes())
}

// WritesOwnBytesKept claims the bytes are as they were.
//
// @Requires b != nil And 0 < |b| And |b| <= 1000
// @Modifies b
// @Ensures r
func WritesOwnBytesKept(b *bytes.Buffer) (r bool) {
	p := b.Bytes()
	first := p[0]
	b.Write(p)
	return p[0] == first // want `postcondition may not hold: r`
}

// ReadsFrom grows the buffer by what a reader returns, which has no entry.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func ReadsFrom(b *bytes.Buffer, r *bytes.Reader) {
	b.ReadFrom(r) // want `cannot verify ReadsFrom: it calls \(\*bytes.Buffer\).ReadFrom, which has no shipped entry`
}

// NB is a type defined over a Buffer, which owns what a Buffer owns.
type NB bytes.Buffer

// HoldsNB holds an NB inline.
type HoldsNB struct{ b NB }

// CopiesHoldsNB copies a struct that holds an NB.
//
// @Ensures True
func CopiesHoldsNB() {
	var x HoldsNB
	y := x // want `copies a value of type HoldsNB, which holds a NB`
	_ = y
}

// WritesNB writes an NB through its conversion, under Modifies p.
//
// @Requires p != nil And |p| <= 1000
// @Modifies p
// @Ensures |p'| = |p| + 1
func WritesNB(p *NB) {
	(*bytes.Buffer)(p).WriteByte('a')
}

// LengthOfInt asks for the length of a number.
//
// @Ensures |n| = 0 // want `n is not a slice, a string, a map, a strings.Builder, or a bytes.Buffer, and has no length`
func LengthOfInt(n int) {}

// WritesBytesUnlisted writes through what Bytes returned, which lies in
// what b owns, without listing b.
//
// @Requires b != nil And 0 < |b|
// @Ensures True
func WritesBytesUnlisted(b *bytes.Buffer) {
	p := b.Bytes()
	p[0] = 'x' // want `p\[0\] is assigned, which WritesBytesUnlisted may not modify; it is memory that Bytes returned, which its contract places within b, and WritesBytesUnlisted passed b as b; list b in a // @Modifies clause`
}

// AppendsBytesUnlisted appends to what Bytes returned, into its capacity,
// which lies in what b owns, without listing b.
//
// @Requires b != nil And |b| <= 1000
// @Ensures True
func AppendsBytesUnlisted(b *bytes.Buffer) {
	p := b.Bytes()
	p = append(p, 'x') // want `which AppendsBytesUnlisted may not modify; it is memory that Bytes returned, which its contract places within b, and AppendsBytesUnlisted passed b as b; list b in a // @Modifies clause`
	_ = p
}

// WritesBytesListed is WritesBytesUnlisted with b listed.
//
// @Requires b != nil And 0 < |b|
// @Modifies b
// @Ensures True
func WritesBytesListed(b *bytes.Buffer) {
	p := b.Bytes()
	p[0] = 'x'
}

// Holder embeds a pointer to a Buffer, whose methods it promotes.
type Holder struct{ *bytes.Buffer }

// Promoted writes through what the promoted Bytes returned, which lies in
// what h.Buffer owns, without listing it.
//
// @Requires h != nil And h.Buffer != nil And 0 < |h.Buffer|
// @Ensures True
func Promoted(h *Holder) {
	p := h.Bytes()
	p[0] = 'x' // want `it is memory that Bytes returned, which its contract places within b, and Promoted passed h.Buffer as b; list h.Buffer in a // @Modifies clause`
}

// PromotedListedInner lists the Buffer the field points to.
//
// @Requires h != nil And h.Buffer != nil And 0 < |h.Buffer|
// @Modifies h.Buffer
// @Ensures True
func PromotedListedInner(h *Holder) {
	p := h.Bytes()
	p[0] = 'x'
}
