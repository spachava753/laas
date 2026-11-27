// Package arrayfields holds arrays of numbers in structs (F42, step 3a):
// the shapes the census found, and the attacks on what the stretch of a
// struct, of one element, and of a slice of an array field cover. Element
// k of an array that begins at the byte A of its allocation lies at A + k.
package arrayfields

// Reader counts symbols, as compress/bzip2's reader holds c [256]uint.
type Reader struct {
	c [256]uint
	n int
}

// Count adds one to the count of a symbol.
//
// @Requires r != nil And r.c[b] < 1000000
// @Modifies r.c
// @Ensures r.c'[b] = r.c[b] + 1
func (r *Reader) Count(b byte) {
	r.c[b]++
}

// Reset zeroes the counts.
//
// @Requires r != nil
// @Modifies r.c
// @Ensures Forall k in [0, 256) : r.c'[k] = 0
func (r *Reader) Reset() {
	// @Invariant Forall k in [0, i) : r.c[k] = 0
	for i := range 256 {
		r.c[i] = 0
	}
}

// KeepsN writes a count and keeps n.
//
// @Requires r != nil
// @Modifies r.c
// @Ensures r.n' = r.n And r.c'[3] = 7
func (r *Reader) KeepsN() {
	r.c[3] = 7
}

// SliceOf writes a count through a slice of the array.
//
// @Requires r != nil
// @Modifies r.c
// @Ensures r.c'[1] = 9 And r.n' = r.n
func (r *Reader) SliceOf() {
	s := r.c[:]
	s[1] = 9
}

// Copy copies the whole array out and back.
//
// @Requires r != nil
// @Modifies r.c
// @Ensures r.c'[7] = r.c[7]
func (r *Reader) Copy() {
	a := r.c
	r.c = a
}

// Lexer remembers widths, as toml's lexer holds prevWidths [4]int.
type Lexer struct {
	prevWidths [4]int
	nprev      int
	pos        int
}

// Backup steps back one rune.
//
// @Requires l != nil And 0 < l.nprev <= 4 And l.pos >= l.prevWidths[l.nprev-1] And l.prevWidths[l.nprev-1] >= 0
// @Modifies l.nprev, l.pos
// @Ensures l.nprev' = l.nprev - 1 And l.pos' = l.pos - l.prevWidths[l.nprev-1]
func (l *Lexer) Backup() {
	l.nprev--
	l.pos -= l.prevWidths[l.nprev]
}

// Push records a width.
//
// @Requires l != nil And 0 <= w < 5
// @Modifies l.prevWidths
// @Ensures l.prevWidths'[0] = w And l.prevWidths'[1] = l.prevWidths[0] And l.prevWidths'[2] = l.prevWidths[1] And l.prevWidths'[3] = l.prevWidths[2]
func (l *Lexer) Push(w int) {
	l.prevWidths[3] = l.prevWidths[2]
	l.prevWidths[2] = l.prevWidths[1]
	l.prevWidths[1] = l.prevWidths[0]
	l.prevWidths[0] = w
}

// Item holds a small array.
type Item struct {
	ID   int
	Vals [4]int64
}

// SumItems sums the first value of each item.
//
// @Requires |xs| < 1000 And (Forall k in [0, |xs|) : 0 <= xs[k].Vals[0] < 1000)
// @Ensures 0 <= result
func SumItems(xs []Item) (result int64) {
	// @Invariant 0 <= result <= 1000 * i
	for i := range xs {
		result += xs[i].Vals[0]
	}
	return result
}

// SetItem writes into one item's array and keeps the next item.
//
// @Requires |xs| > 1
// @Modifies xs
// @Ensures xs'[0].Vals[2] = 5 And xs'[1].Vals[2] = xs[1].Vals[2] And xs'[0].ID = xs[0].ID
func SetItem(xs []Item) {
	xs[0].Vals[2] = 5
}

// Through writes an element of a slice made over a field and keeps the
// next item.
//
// @Requires |xs| > 1
// @Modifies xs
// @Ensures xs'[1].Vals[0] = xs[1].Vals[0] And xs'[0].Vals[3] = 4
func Through(xs []Item) {
	s := xs[0].Vals[:]
	s[3] = 4
}

// set writes one value of the first item.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0].Vals[1] = 3
func set(xs []Item) {
	xs[0].Vals[1] = 3
}

// CallerKeeps calls set on a subslice and keeps the item before it.
//
// @Requires |xs| > 2
// @Modifies xs
// @Ensures xs'[0].Vals[1] = xs[0].Vals[1] And xs'[1].Vals[1] = 3
func CallerKeeps(xs []Item) {
	set(xs[1:])
}

// LoopKeeps zeroes a value of each item of the tail and keeps the head.
//
// @Requires |xs| > 2
// @Modifies xs
// @Ensures xs'[0].Vals[3] = xs[0].Vals[3]
func LoopKeeps(xs []Item) {
	t := xs[1:]
	// @Invariant True
	for i := range t {
		t[i].Vals[3] = 0
	}
}

// Holder holds items and a count.
type Holder struct {
	N     int64
	Items []Item
}

// HolderKeeps writes through the holder's items and keeps N.
//
// @Requires h != nil And |h.Items| > 0
// @Modifies h.Items
// @Ensures h.N' = h.N And h.Items'[0].Vals[0] = 9
func HolderKeeps(h *Holder) {
	h.Items[0].Vals[0] = 9
}

// Pair holds two arrays side by side.
type Pair struct {
	A [3]int64
	B [3]int64
}

// Apart writes A and keeps B.
//
// @Requires p != nil
// @Modifies p.A
// @Ensures p.B'[0] = p.B[0] And p.A'[2] = 1
func Apart(p *Pair) {
	p.A[2] = 1
}
