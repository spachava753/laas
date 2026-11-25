// Package copies holds programs over the built-in copy: slices of numbers
// and booleans, and a string into a []byte, with overlapping operands
// copied as memmove copies them.
package copies

// Fill copies a slice into an array.
//
// @Requires |p| >= 4
// @Ensures r[0] = p[0] And r[3] = p[3] And n = 4
func Fill(p []byte) (r [4]byte, n int) {
	n = copy(r[:], p)
	return r, n
}

// The number copied is the shorter length.
//
// @Ensures n = |dst| Or n = |src|
// @Ensures n <= |dst| And n <= |src|
// @Modifies dst
func Count(dst, src []int) (n int) {
	return copy(dst, src)
}

// Copy copies every element of src into dst.
//
// @Requires |dst| = |src|
// @Modifies dst
// @Ensures Forall k in [0, |src|) : dst'[k] = src[k]
func Copy(dst, src []int) {
	copy(dst, src)
}

// The elements after the copied ones are as they were.
//
// @Requires |dst| = 4 And |src| = 2
// @Modifies dst
// @Ensures dst'[0] = src[0] And dst'[2] = dst[2] And dst'[3] = dst[3]
func Shorter(dst, src []int) {
	copy(dst, src)
}

// Both orders of two slices.
//
// @Requires |a| = 2 And |b| = 2
// @Modifies a, b
// @Ensures a'[0] = b[0] And b'[0] = b[0]
func AThenB(a, b []int) {
	copy(a, b)
	copy(b, a)
}

// @Requires |a| = 2 And |b| = 2
// @Modifies a, b
// @Ensures b'[0] = a[0] And a'[0] = a[0]
func BThenA(a, b []int) {
	copy(b, a)
	copy(a, b)
}

// Shift moves a buffer down over itself, as memmove does.
//
// @Requires 0 <= n <= |buf|
// @Modifies buf
// @Ensures r = |buf| - n
// @Ensures Forall k in [0, |buf| - n) : buf'[k] = buf[k + n]
func Shift(buf []byte, n int) (r int) {
	return copy(buf, buf[n:])
}

// ShiftUp moves a buffer up over itself.
//
// @Requires |buf| = 4
// @Modifies buf
// @Ensures buf'[1] = buf[0] And buf'[2] = buf[1] And buf'[3] = buf[2] And buf'[0] = buf[0]
func ShiftUp(buf []byte) {
	copy(buf[1:], buf)
}

// A string into a byte slice.
//
// @Requires |dst| >= 2
// @Modifies dst
// @Ensures dst'[0] = 104 And dst'[1] = 105 And n = 2
func FromString(dst []byte) (n int) {
	return copy(dst, "hi")
}

// The destination is a slice of the source's array.
//
// @Ensures r = 1 And s = 1
func SameArray() (r, s int) {
	a := [4]int{1, 2, 3, 4}
	copy(a[2:], a[:])
	return a[2], a[0]
}

// A nil operand copies nothing.
//
// @Ensures n = 0
func Nil(dst []int) (n int) {
	var none []int
	return copy(dst, none)
}

// copy in a loop writes the destination at each iteration.
//
// @Requires |dst| = 4 And |src| = 4
// @Modifies dst
// @Ensures Forall k in [0, 4) : dst'[k] = src[k]
func InLoop(dst, src []int) {
	// @Invariant 0 <= i <= 4
	// @Invariant Forall k in [0, i) : dst[k] = src[k]
	for i := range 4 {
		copy(dst[i:i+1], src[i:i+1])
	}
}

// The trial's decoder fills its array from the slice it holds.
type decoder struct {
	in  []byte
	arr [8]byte
}

// @Requires d != nil And |d.in| <= 8
// @Requires apart(d.in, d.arr)
// @Modifies d
// @Ensures n = |d.in| And (|d.in| = 0 Or d.arr'[0] = d.in'[0])
func (d *decoder) Refill() (n int) {
	return copy(d.arr[:], d.in)
}

// @Ensures r = 2
func RefillOverlap() (r byte) {
	var d decoder
	d.arr[0], d.arr[1] = 1, 2
	d.in = d.arr[1:3]
	copy(d.arr[:], d.in)
	return d.arr[0]
}
