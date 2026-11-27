// Package arrayptrs holds pointers to arrays of numbers in local variables
// (F42, step 3a): made by &a, &s.f, new, and a conversion of a slice, and
// used by indexing, *p, slicing, len, cap, range, and comparison.
package arrayptrs

// Block holds a block of words.
type Block struct {
	N    int
	Word [4]uint32
}

// SetWord writes a word through a pointer to the block's array.
//
// @Requires b != nil
// @Modifies b.Word
// @Ensures b.Word'[2] = 7 And b.Word'[1] = b.Word[1] And b.N' = b.N
func SetWord(b *Block) {
	p := &b.Word
	p[2] = 7
}

// Local fills a local array through a pointer to it.
//
// @Ensures r = 6
func Local() (r uint32) {
	var a [4]uint32
	p := &a
	// @Invariant Forall k in [0, i) : a[k] = k
	for i := range p {
		p[i] = uint32(i)
	}
	return a[1] + a[2] + a[3]
}

// Fresh makes an array with new and counts its length.
//
// @Ensures r = 8
func Fresh() (r int) {
	p := new([8]int)
	p[7] = 1
	return len(p) + cap(p) - 8
}

// FromSlice converts a slice to a pointer to its first four elements and
// writes through it.
//
// @Requires |xs| >= 4
// @Modifies xs
// @Ensures xs'[3] = 9 And xs'[0] = xs[0]
func FromSlice(xs []int16) {
	p := (*[4]int16)(xs)
	p[3] = 9
}

// Whole copies the array a pointer points to and writes it back.
//
// @Requires b != nil
// @Modifies b.Word
// @Ensures b.Word'[0] = 1 And b.Word'[3] = b.Word[3]
func Whole(b *Block) {
	p := &b.Word
	w := *p
	w[0] = 1
	*p = w
}

// Sliced slices the array through the pointer.
//
// @Requires b != nil
// @Modifies b.Word
// @Ensures b.Word'[1] = 5
func Sliced(b *Block) {
	p := &b.Word
	s := p[1:3]
	s[0] = 5
}

// NilLen is the length of a nil pointer to an array, which Go gives as
// the array's length.
//
// @Ensures r = 4
func NilLen() (r int) {
	var p *[4]int
	return len(p)
}

// NilRange ranges over the indices of a nil pointer to an array, which Go
// does without reading it.
//
// @Ensures r = 4
func NilRange() (r int) {
	var p *[4]int
	// @Invariant r = i
	for i := range p {
		r = i + 1
	}
	return r
}

// Same compares two pointers to one array.
//
// @Requires b != nil
// @Ensures r
func Same(b *Block) (r bool) {
	p, q := &b.Word, &b.Word
	return p == q && p != nil
}
