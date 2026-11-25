package arrays

// Each function here claims something false, or does something that may
// panic, and is refused.

// @Ensures r = 4
func FillWrong() (r byte) {
	var buf [8]byte
	// @Invariant 0 <= i <= 8
	// @Invariant Forall k in [0, i) : buf[k] = k
	for i := range buf {
		buf[i] = byte(i)
	}
	return buf[3] // want `postcondition may not hold: r = 4`
}

// @Ensures r = 4
func FillBoxedWrong() (r byte) {
	var buf [8]byte
	// @Invariant 0 <= i <= 8
	// @Invariant Forall k in [0, i) : buf[k] = k
	for i := range buf {
		buf[i] = byte(i)
	}
	_ = peek(buf[:])
	return buf[3] // want `postcondition may not hold: r = 4`
}

// The copy is written, not the original.
//
// @Ensures r = 9
func CopyWrong() (r int) {
	a := [3]int{1, 2, 3}
	b := a
	b[0] = 9
	return a[0] // want `postcondition may not hold: r = 9`
}

// @Ensures r = 9
func CopyBoxedWrong() (r int) {
	a := [3]int{1, 2, 3}
	b := a
	b[0] = 9
	_ = peekInts(a[:])
	return a[0] // want `postcondition may not hold: r = 9`
}

// A copy taken before the write through the slice keeps the old value.
//
// @Ensures r = 9
func CopyKeepsWrong() (r byte) {
	var a [2]byte
	t := a[:]
	b := a
	t[0] = 9
	return b[0] // want `postcondition may not hold: r = 9`
}

// The write through the slice is seen through the array.
//
// @Ensures r = 0
func ThroughSliceWrong() (r byte) {
	var buf [4]byte
	put(buf[1:], 7)
	return buf[1] // want `postcondition may not hold: r = 0`
}

// The array is written, and the slice sees it.
//
// @Ensures r = 0
func ThroughArrayWrong() (r byte) {
	var buf [4]byte
	t := buf[:]
	buf[3] = 8
	return t[3] // want `postcondition may not hold: r = 0`
}

// The two slices share an element.
//
// @Ensures r = 1
func OverlapWrong() (r byte) {
	var buf [4]byte
	a, b := buf[0:3], buf[1:4]
	a[1] = 1
	b[0] = 2
	return a[1] // want `postcondition may not hold: r = 1`
}

// The append writes the array in place.
//
// @Ensures r = 0
func AppendInPlaceWrong() (r byte) {
	var buf [4]byte
	t := append(buf[:1], 5)
	_ = t
	return buf[1] // want `postcondition may not hold: r = 0`
}

// The append moves, so the array keeps its zero.
//
// @Ensures r = 5
func AppendMovesWrong() (r byte) {
	var buf [4]byte
	t := append(buf[:], 5)
	_ = t
	return buf[0] // want `postcondition may not hold: r = 5`
}

// The range is over a copy, so c is the element as it was.
//
// @Ensures r = 5
func RangeCopyWrong() (r int) {
	a := [2]int{1, 2}
	// @Invariant 0 <= i <= 2
	for i, c := range a {
		a[1] = 5
		if i == 1 {
			r = c
		}
	}
	return r // want `postcondition may not hold: r = 5`
}

// @Ensures r = 5
func RangeCopyBoxedWrong() (r int) {
	a := [2]int{1, 2}
	_ = peekInts(a[:])
	// @Invariant 0 <= i <= 2
	for i, c := range a {
		a[1] = 5
		if i == 1 {
			r = c
		}
	}
	return r // want `postcondition may not hold: r = 5`
}

// The two arrays are apart.
//
// @Ensures s = 1
func TwoArraysWrong() (r, s byte) {
	var a, b [4]byte
	a[0] = 1
	b[0] = 2
	return a[0], b[0] // want `postcondition may not hold: s = 1`
}

// @Ensures s = 1
func TwoArraysBoxedWrong() (r, s byte) {
	var a, b [4]byte
	_ = peek(a[:])
	_ = peek(b[:])
	a[0] = 1
	b[0] = 2
	return a[0], b[0] // want `postcondition may not hold: s = 1`
}

// The index may be out of range.
//
// @Requires 0 <= i
// @Ensures True
func IndexOut(i int) (r byte) {
	var buf [8]byte
	return buf[i] // want `index may be out of range`
}

// @Requires 0 <= i
// @Ensures True
func IndexOutBoxed(i int) (r byte) {
	var buf [8]byte
	_ = peek(buf[:])
	return buf[i] // want `index may be out of range`
}

// @Requires 0 <= i
// @Ensures True
func StoreOut(i int) {
	var buf [8]byte
	buf[i] = 1 // want `index may be out of range`
	_ = buf
}

// @Requires 0 <= i
// @Ensures True
func StoreOutBoxed(i int) {
	var buf [8]byte
	_ = peek(buf[:])
	buf[i] = 1 // want `index may be out of range`
}

// An array of length zero has no element.
//
// @Ensures True
func ZeroIndex(i int) (r int) {
	var z [0]int
	return z[i] // want `index may be negative` `index may be out of range`
}

// A slice of an array may not go past its end.
//
// @Requires 0 <= n
// @Ensures True
func SliceOut(n int) (r int) {
	var buf [8]byte
	return peek(buf[:n]) // want `slice bounds may be out of range`
}

// Two arrays of floats may hold a NaN, which is not equal to itself.
//
// @Ensures r
func FloatEqual(a [2]float64) (r bool) {
	return a == a // want `postcondition may not hold: r`
}

// The conversion panics when the slice is shorter than the array.
//
// @Ensures True
func ConvertShort(p []byte) (r [4]byte) {
	return [4]byte(p) // want `the conversion may panic: p may be shorter than \[4\]byte`
}

// The other elements of a literal are zero.
//
// @Ensures r[1] = 7
func KeyedWrong() (r [4]int) {
	return [4]int{2: 7} // want `postcondition may not hold: r\[1\] = 7`
}

// The hash has 32 bytes, so its digits are 64.
//
// @Ensures |result| = 32
func DigestWrong(data []byte) (result string) {
	hash := [32]byte{}
	_ = data
	return hexOf(hash[:]) // want `postcondition may not hold: \|result\| = 32`
}

// @Requires 2 * |p| <= MaxAlloc
// @Ensures |r| = 2 * |p|
func hexOf(p []byte) (r string) {
	out := make([]byte, 2*len(p))
	return string(out)
}

// The literal writes into a copy of nothing: it assigns the array itself.
//
// @Ensures r = 0
func CapturedWrong() (r int) {
	var a [2]int
	set := func() { a[1] = 4 }
	set()
	return a[1] // want `postcondition may not hold: r = 0`
}

// The deferred write through the slice reaches the result.
//
// @Ensures r[0] = 0
func DeferredWriteWrong() (r [4]int) {
	s := r[:]
	defer func() { s[0] = 1 }()
	return r // want `postcondition may not hold: r\[0\] = 0`
}

// A slice of a local array of length zero is not nil.
//
// @Ensures r
func ZeroSliceWrong() (r bool) {
	var z [0]byte
	return z[:] == nil // want `postcondition may not hold: r`
}

// The copy overwrites what b held.
//
// @Ensures r = 0
func CopyIntoWrong() (r int) {
	var a, b [2]int
	_, _ = peekInts(a[:]), peekInts(b[:])
	a[0] = 1
	b = a
	return b[0] // want `postcondition may not hold: r = 0`
}

// A copy taken before a write through a slice of the original holds the
// elements as they were, each at its own index.
//
// @Ensures r = 2
func CopyKeepsElementsWrong() (r byte) {
	a := [2]byte{1, 2}
	t := a[:]
	b := a
	t[0] = 9
	return b[0] // want `postcondition may not hold: r = 2`
}

// The last index is one less than the length.
//
// @Requires 0 <= i <= 8
// @Ensures True
func IndexEdge(i int) (r byte) {
	var buf [8]byte
	return buf[i] // want `index may be out of range`
}

// @Requires 0 <= i <= 8
// @Ensures True
func IndexEdgeBoxed(i int) (r byte) {
	var buf [8]byte
	_ = peek(buf[:])
	return buf[i] // want `index may be out of range`
}

// @Requires 0 <= i <= 8
// @Ensures True
func StoreEdge(i int) (r byte) {
	var buf [8]byte
	buf[i] = 1 // want `index may be out of range`
	return buf[0]
}

// @Requires 0 <= i <= 8
// @Ensures True
func StoreEdgeBoxed(i int) {
	var buf [8]byte
	_ = peek(buf[:])
	buf[i] = 1 // want `index may be out of range`
}
