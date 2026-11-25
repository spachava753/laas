package arraystructs

import "io"

// Each function here claims something false, may panic, or uses what is
// not supported, and is refused.

// The write of an element changes it.
//
// @Requires b != nil
// @Modifies b
// @Ensures b.out'[1] = b.out[1]
func PutWrong(b *buffer) {
	b.out[1] = 7
} // want `postcondition may not hold: b\.out'\[1\] = b\.out\[1\]`

// A callee that writes the array may write any element of it.
//
// @Requires b != nil
// @Modifies b
// @Ensures b.out'[0] = b.out[0]
func FillAllWrong(b *buffer) {
	fill(b.out[:], 9)
} // want `postcondition may not hold: b\.out'\[0\] = b\.out\[0\]`

// The capacity of a slice of the array runs to its end.
//
// @Requires b != nil
// @Modifies b
// @Ensures b.out'[4] = b.out[4]
func FillHeadWrong(b *buffer) {
	fill(b.out[:4], 9)
} // want `postcondition may not hold: b\.out'\[4\] = b\.out\[4\]`

// A function that writes the array lists the struct.
//
// @Requires b != nil
// @Ensures True
func Unlisted(b *buffer) {
	b.out[0] = 1 // want `b\.out\[0\] is assigned, which Unlisted may not modify; list it in a // @Modifies clause, as b\.out`
}

// The two pointers may be one.
//
// @Requires a != nil And b != nil
// @Modifies a, b
// @Ensures a.out'[0] = 1
func SameWrong(a, b *buffer) {
	a.out[0] = 1
	b.out[0] = 2
} // want `postcondition may not hold: a\.out'\[0\] = 1`

// The copy keeps the old element.
//
// @Requires b != nil
// @Modifies b
// @Ensures r = 5
func CopyStructWrong(b *buffer) (r byte) {
	saved := *b
	b.out[0] = 5
	return saved.out[0] // want `postcondition may not hold: r = 5`
}

// The copy of a struct value is a copy.
//
// @Ensures r = 4
func ValueWrong() (r byte) {
	var x buffer
	x.out[2] = 3
	y := x
	y.out[2] = 4
	return x.out[2] // want `postcondition may not hold: r = 4`
}

// A caller that hands a slice of the buffer's own array breaks apart.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func CopyInOverlap(b *buffer) {
	b.copyIn(b.out[:2]) // want `precondition of copyIn may not hold: apart\(p, b\.out\)`
}

// copyInUnchecked does not say that p is apart from the array.
//
// @Requires b != nil And |p| <= 16
// @Modifies b
// @Ensures Forall k in [0, |p|) : b.out'[k] = p[k]
func (b *buffer) copyInUnchecked(p []byte) {
	// @Invariant 0 <= i <= |p|
	// @Invariant Forall k in [0, i) : b.out[k] = p[k]
	for i := range p { // want `loop invariant may not be preserved: Forall k in \[0, i\) : b\.out\[k\] = p\[k\]`
		b.out[i] = p[i]
	}
} // want `postcondition may not hold: Forall k in \[0, \|p\|\) : b\.out'\[k\] = p\[k\]`

// A slice of an array field and a parameter of the same element type are
// separate only when the caller says so.
//
// @Requires b != nil
// @Modifies b, p
// @Ensures True
func HandsBoth(b *buffer, p []byte) {
	fill2(b.out[:], p) // want `the slices passed to fill2 as a and b may overlap`
}

// @Modifies a
// @Ensures True
func fill2(a, b []byte) {
	if len(a) > 0 {
		a[0] = 1
	}
}

// An index out of range of the field.
//
// @Requires b != nil And 0 <= i <= 16
// @Modifies b
// @Ensures True
func PutEdge(b *buffer, i int) {
	b.out[i] = 1 // want `index may be out of range`
}

// @Requires b != nil And 0 <= i <= 16
// @Ensures True
func GetEdge(b *buffer, i int) (r byte) {
	return b.out[i] // want `index may be out of range`
}

// Slicing or copying an array field reads the struct, which a nil pointer
// does not have, also for an array of length zero.
//
// @Ensures True
func SliceNil(b *buffer) (r []byte) {
	return b.out[:] // want `pointer may be nil`
}

type empty struct {
	z [0]byte
}

// @Ensures True
func SliceNilZero(p *empty) (r []byte) {
	return p.z[:] // want `pointer may be nil`
}

// @Ensures True
func CopyNil(b *buffer) (r [16]byte) {
	return b.out // want `pointer may be nil`
}

// @Ensures True
func RangeNil(b *buffer) (r int) {
	for _, c := range b.out { // want `pointer may be nil`
		r = int(c)
	}
	return r
}

// The invariant of digits is kept only for a digit.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func (p *digits) PushAny(c byte) {
	if p.n < 4 {
		p.d[p.n] = c
		p.n++
	}
} // want `invariant of digits may not hold for p on return: Forall k in \[0, 4\) : d\[k\] < 10; it was not kept from entry, `

// Modifies names an array field, not an element.
//
// @Requires b != nil
// @Modifies b.out[0] // want `in Modifies annotation: b\.out\[0\] is an element of an array; Modifies names the array, b\.out`
// @Ensures True
func ElementTarget(b *buffer) {
	b.out[0] = 1
}

// A write through what h.w holds may write h, so a fact about h's array
// does not survive it (F4 of the design review).
type dumper struct {
	w   io.Writer
	buf [4]byte
}

// @Requires h != nil And h.w != nil
// @Modifies h, h.w
// @Ensures h.buf'[0] = 7
func (h *dumper) Write() {
	h.buf[0] = 7
	h.w.Write(h.buf[:1])
} // want `postcondition may not hold: h\.buf'\[0\] = 7`

// The second write is to the other array of the struct.
//
// @Requires p != nil
// @Modifies p
// @Ensures p.a'[0] = 2
func (p *pair) SetWrong() {
	p.a[0] = 1
	p.b[0] = 2
} // want `postcondition may not hold: p.a'\[0\] = 2`

type boxedBytes struct {
	A [4]byte
}

// Overwriting the struct overwrites the array, which the slice may be a
// view of.
//
// @Requires p != nil And |s| = 1 And s[0] = 7
// @Modifies p, s
// @Ensures result = 7
func ResetBoxedBytes(p *boxedBytes, s []byte) (result byte) {
	*p = boxedBytes{}
	return s[0] // want `postcondition may not hold: result = 7`
}

// The same, through a call that writes the struct.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func resetBytes(p *boxedBytes) {
	*p = boxedBytes{}
}

// @Requires p != nil And |s| = 1 And s[0] = 7
// @Modifies p, s
// @Ensures result = 7
func ResetBoxedBytesCall(p *boxedBytes, s []byte) (result byte) {
	resetBytes(p)
	return s[0] // want `postcondition may not hold: result = 7`
}

// The first element alone still lies in the array.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func CopyInOverlapFirst(b *buffer) {
	b.copyIn(b.out[:1:1]) // want `precondition of copyIn may not hold: apart\(p, b.out\)`
}
