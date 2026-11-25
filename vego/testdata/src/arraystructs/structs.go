// Package arraystructs holds programs over structs that hold arrays of
// one-byte elements: written through a pointer, sliced, copied, held in a
// slice of structs, and handed to callees.
package arraystructs

// buffer holds a count and an array.
type buffer struct {
	n   int
	out [16]byte
}

// Put writes one element and leaves the other field.
//
// @Requires b != nil And 0 <= i < 16
// @Modifies b
// @Ensures b.out'[i] = c And b.n' = b.n
// @Ensures Forall k in [0, 16) : k != i -> b.out'[k] = b.out[k]
func (b *buffer) Put(i int, c byte) {
	b.out[i] = c
}

// Count writes the other field and leaves the array.
//
// @Requires b != nil And b.n < 100
// @Modifies b
// @Ensures b.n' = b.n + 1 And Forall k in [0, 16) : b.out'[k] = b.out[k]
func (b *buffer) Count() {
	b.n++
}

// Both calls are seen through the pointer, in both orders.
//
// @Requires b != nil And b.n < 100
// @Modifies b
// @Ensures b.out'[1] = 7 And b.n' = b.n + 1
func PutThenCount(b *buffer) {
	b.Put(1, 7)
	b.Count()
}

// @Requires b != nil And b.n < 100
// @Modifies b
// @Ensures b.out'[1] = 7 And b.n' = b.n + 1
func CountThenPut(b *buffer) {
	b.Count()
	b.Put(1, 7)
}

// fill writes c into every element of p.
//
// @Modifies p
// @Ensures Forall k in [0, |p|) : p'[k] = c
func fill(p []byte, c byte) {
	// @Invariant 0 <= i <= |p|
	// @Invariant Forall k in [0, i) : p[k] = c
	for i := range p {
		p[i] = c
	}
}

// A slice of the array handed to a callee writes the array and nothing
// else of the struct.
//
// @Requires b != nil
// @Modifies b
// @Ensures b.out'[0] = 9 And b.out'[15] = 9 And b.n' = b.n
func FillAll(b *buffer) {
	fill(b.out[:], 9)
}

// A part of the array handed on writes that part.
//
// @Requires b != nil
// @Modifies b
// @Ensures b.out'[3] = 9 And b.out'[4] = b.out[4]
func FillHead(b *buffer) {
	fill(b.out[:4:4], 9)
}

// copyIn writes p into the start of the buffer's array.
//
// @Requires b != nil And |p| <= 16
// @Requires apart(p, b.out)
// @Modifies b
// @Ensures Forall k in [0, |p|) : b.out'[k] = p[k]
func (b *buffer) copyIn(p []byte) {
	// @Invariant 0 <= i <= |p|
	// @Invariant Forall k in [0, i) : b.out[k] = p[k]
	for i := range p {
		b.out[i] = p[i]
	}
}

// A slice that the caller made is apart from the array.
//
// @Requires b != nil
// @Modifies b
// @Ensures b.out'[1] = 2
func CopyIn(b *buffer) {
	p := []byte{1, 2}
	b.copyIn(p)
}

// Two buffers, apart from each other.
//
// @Requires a != nil And b != nil And a != b
// @Modifies a, b
// @Ensures a.out'[0] = 1 And b.out'[0] = 2
func Two(a, b *buffer) {
	a.out[0] = 1
	b.out[0] = 2
}

// @Requires a != nil And b != nil And a != b
// @Modifies a, b
// @Ensures a.out'[0] = 1 And b.out'[0] = 2
func TwoOtherOrder(a, b *buffer) {
	b.out[0] = 2
	a.out[0] = 1
}

// The two pointers may be one: the later write wins.
//
// @Requires a != nil And b != nil
// @Modifies a, b
// @Ensures b.out'[0] = 2
func Same(a, b *buffer) {
	a.out[0] = 1
	b.out[0] = 2
}

// A copy of the struct holds the array as it was.
//
// @Requires b != nil
// @Modifies b
// @Ensures r = old(b.out[0]) And b.out'[0] = 5
func CopyStruct(b *buffer) (r byte) {
	saved := *b
	b.out[0] = 5
	return saved.out[0]
}

// A struct value with an array, written and copied.
//
// @Ensures r = 3 And s = 4
func Value() (r, s byte) {
	var x buffer
	x.out[2] = 3
	y := x
	y.out[2] = 4
	return x.out[2], y.out[2]
}

// A struct value whose array is sliced lives in memory.
//
// @Ensures r = 9
func ValueSliced() (r byte) {
	var x buffer
	fill(x.out[:], 9)
	return x.out[5]
}

// A literal with an array field.
//
// @Ensures r = 2 And s = 0 And t = 1
func Literal() (r, s byte, t int) {
	x := buffer{n: 1, out: [16]byte{0: 2}}
	return x.out[0], x.out[1], x.n
}

// Elements of a slice of structs that hold arrays.
//
// @Requires |bs| >= 2
// @Modifies bs
// @Ensures bs'[1].out[0] = 1 And bs'[0].out[0] = bs[0].out[0]
func InSlice(bs []buffer) {
	bs[1].out[0] = 1
}

// The length of an array field is a constant, and a range over it with no
// value does not read the struct, so neither needs the pointer.
//
// @Ensures r = 16
func Length(b *buffer) (r int) {
	for i := range b.out {
		_ = i
	}
	return len(b.out)
}

// An array of booleans in a struct.
type seen struct {
	marks [8]bool
}

// @Requires s != nil
// @Modifies s
// @Ensures s.marks'[2]
func (s *seen) Mark() {
	s.marks[2] = true
}

// The invariant of a type over its array.
//
// @Invariant 0 <= n <= 4
// @Invariant Forall k in [0, 4) : d[k] < 10
type digits struct {
	d [4]byte
	n int
}

// @Requires p != nil And c < 10
// @Modifies p
// @Ensures True
func (p *digits) Push(c byte) {
	if p.n < 4 {
		p.d[p.n] = c
		p.n++
	}
}

// Appending into the array of a struct in place.
//
// @Requires b != nil
// @Modifies b
// @Ensures b.out'[1] = 7 And |r| = 2
func AppendInto(b *buffer) (r []byte) {
	return append(b.out[:1], 7)
}

// Modifies names the array field alone.
//
// @Requires b != nil
// @Modifies b.out
// @Ensures b.out'[0] = 1
func Field(b *buffer) {
	b.out[0] = 1
}

// @Requires b != nil
// @Modifies b.out
// @Ensures b.n' = b.n And b.out'[0] = 1
func KeepsCount(b *buffer) {
	Field(b)
}

// Two arrays in one struct lie apart, each at its own field.
type pair struct {
	a [4]byte
	b [4]byte
}

// @Requires p != nil
// @Modifies p
// @Ensures p.a'[0] = 1 And p.b'[0] = 2 And p.a'[3] = p.a[3]
func (p *pair) Set() {
	p.a[0] = 1
	p.b[0] = 2
}

// Two buffers written at different indices.
//
// @Requires a != nil And b != nil And a != b
// @Modifies a, b
// @Ensures a.out'[0] = 1 And b.out'[1] = 2
func TwoIndices(a, b *buffer) {
	a.out[0] = 1
	b.out[1] = 2
}

// A write to one buffer keeps an element of another, read only.
//
// @Requires a != nil And b != nil And a != b
// @Modifies b
// @Ensures r = old(a.out[0])
func ReadOther(a, b *buffer) (r byte) {
	b.out[1] = 2
	return a.out[0]
}
