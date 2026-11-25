// Package arrays holds programs over arrays of numbers and booleans. Each
// ordinary program comes twice: as written, where the array is a value, and
// with a slice of the array handed to a callee that only reads it, which
// puts the array in memory. Both forms get the same verdicts.
package arrays

// @Ensures r = |p|
func peek(p []byte) (r int) { return len(p) }

// @Ensures r = |p|
func peekInts(p []int) (r int) { return len(p) }

// Fill writes every element and reads one back.
//
// @Ensures r = 3
func Fill() (r byte) {
	var buf [8]byte
	// @Invariant 0 <= i <= 8
	// @Invariant Forall k in [0, i) : buf[k] = k
	for i := range buf {
		buf[i] = byte(i)
	}
	return buf[3]
}

// @Ensures r = 3
func FillBoxed() (r byte) {
	var buf [8]byte
	// @Invariant 0 <= i <= 8
	// @Invariant Forall k in [0, i) : buf[k] = k
	for i := range buf {
		buf[i] = byte(i)
	}
	_ = peek(buf[:])
	return buf[3]
}

// Sum adds the elements of an array parameter.
//
// @Requires Forall k in [0, 4) : 0 <= a[k] <= 1000
// @Ensures 0 <= r <= 4000
func Sum(a [4]int) (r int) {
	// @Invariant 0 <= i <= 4
	// @Invariant 0 <= r <= 1000 * i
	for i := range a {
		r += a[i]
	}
	return r
}

// @Requires Forall k in [0, 4) : 0 <= a[k] <= 1000
// @Ensures 0 <= r <= 4000
func SumBoxed(a [4]int) (r int) {
	_ = peekInts(a[:])
	// @Invariant 0 <= i <= 4
	// @Invariant 0 <= r <= 1000 * i
	for i := range a {
		r += a[i]
	}
	return r
}

// SumValues ranges over the elements.
//
// @Requires Forall k in [0, 4) : 0 <= a[k] <= 1000
// @Ensures 0 <= r <= 4000
func SumValues(a [4]int) (r int) {
	// @Invariant 0 <= i <= 4
	// @Invariant 0 <= r <= 1000 * i
	for i, c := range a {
		_ = i
		r += c
	}
	return r
}

// @Requires Forall k in [0, 4) : 0 <= a[k] <= 1000
// @Ensures 0 <= r <= 4000
func SumValuesBoxed(a [4]int) (r int) {
	_ = peekInts(a[:])
	// @Invariant 0 <= i <= 4
	// @Invariant 0 <= r <= 1000 * i
	for i, c := range a {
		_ = i
		r += c
	}
	return r
}

// Copy shows that assignment copies: writing the copy leaves the original.
//
// @Ensures r = 1 And s = 9
func Copy() (r, s int) {
	a := [3]int{1, 2, 3}
	b := a
	b[0] = 9
	return a[0], b[0]
}

// @Ensures r = 1 And s = 9 And t = 2
func CopyBoxed() (r, s, t int) {
	a := [3]int{1, 2, 3}
	b := a
	b[0] = 9
	_ = peekInts(a[:])
	_ = peekInts(b[:])
	return a[0], b[0], b[1]
}

// Assigning an array in memory to another overwrites it.
//
// @Ensures r = 1 And s = 2
func CopyInto() (r, s int) {
	var a, b [2]int
	_, _ = peekInts(a[:]), peekInts(b[:])
	a[0], a[1] = 1, 2
	b = a
	return b[0], b[1]
}

// Two arrays written in both orders stay apart.
//
// @Ensures r = 1 And s = 2
func TwoArrays() (r, s byte) {
	var a, b [4]byte
	a[0] = 1
	b[0] = 2
	return a[0], b[0]
}

// @Ensures r = 1 And s = 2
func TwoArraysOtherOrder() (r, s byte) {
	var a, b [4]byte
	b[0] = 2
	a[0] = 1
	return a[0], b[0]
}

// @Ensures r = 1 And s = 2
func TwoArraysBoxed() (r, s byte) {
	var a, b [4]byte
	a[0] = 1
	b[0] = 2
	_ = peek(a[:])
	_ = peek(b[:])
	return a[0], b[0]
}

// @Ensures r = 1 And s = 2
func TwoArraysBoxedOtherOrder() (r, s byte) {
	var a, b [4]byte
	_ = peek(b[:])
	_ = peek(a[:])
	b[0] = 2
	a[0] = 1
	return a[0], b[0]
}

// Make returns an array by value.
//
// @Ensures |r| = 4 And r[2] = 7 And r[0] = 0
func Make() (r [4]int) {
	return [4]int{2: 7}
}

// @Ensures |r| = 4 And r[2] = 7 And r[0] = 0
func MakeBoxed() (r [4]int) {
	a := [4]int{2: 7}
	_ = peekInts(a[:])
	return a
}

// Use calls Make and reads what it returned.
//
// @Ensures r = 7
func Use() (r int) {
	a := Make()
	return a[2]
}

// @Ensures r = 7
func UseBoxed() (r int) {
	a := MakeBoxed()
	_ = peekInts(a[:])
	return a[2]
}

// Literals with their length counted and with keys.
//
// @Ensures r = 6
func Literals() (r int) {
	a := [...]int{1, 2, 3}
	b := [5]int{4: 2, 1: 1}
	return a[2] + b[4] + b[1]
}

// @Ensures r = 6
func LiteralsBoxed() (r int) {
	a := [...]int{1, 2, 3}
	b := [5]int{4: 2, 1: 1}
	_ = peekInts(a[:])
	_ = peekInts(b[:])
	return a[2] + b[4] + b[1]
}

// Equal compares two arrays.
//
// @Ensures r <-> (a[0] = b[0] And a[1] = b[1])
func Equal(a, b [2]byte) (r bool) {
	return a == b
}

// @Ensures r <-> (a[0] = b[0] And a[1] = b[1])
func EqualBoxed(a, b [2]byte) (r bool) {
	_ = peek(a[:])
	_ = peek(b[:])
	return a == b
}

// @Ensures r <-> a = b
func EqualFormula(a, b [2]bool) (r bool) {
	return a == b
}

// Index is in range by its requires and the length of the type.
//
// @Requires 0 <= i < 8
// @Ensures r = 0
func Index(i int) (r byte) {
	var buf [8]byte
	return buf[i]
}

// @Requires 0 <= i < 8
// @Ensures r = 0
func IndexBoxed(i int) (r byte) {
	var buf [8]byte
	_ = peek(buf[:])
	return buf[i]
}

// RangeCopy ranges over a copy of the array, taken before the first
// iteration, so the write in the body is not seen by the loop.
//
// @Ensures r = 2
func RangeCopy() (r int) {
	a := [2]int{1, 2}
	// @Invariant 0 <= i <= 2
	// @Invariant i = 2 -> r = 2
	for i, c := range a {
		a[1] = 5
		if i == 1 {
			r = c
		}
	}
	return r
}

// @Ensures r = 2
func RangeCopyBoxed() (r int) {
	a := [2]int{1, 2}
	_ = peekInts(a[:])
	// @Invariant 0 <= i <= 2
	// @Invariant i = 2 -> r = 2
	for i, c := range a {
		a[1] = 5
		if i == 1 {
			r = c
		}
	}
	return r
}

// Length is a constant.
//
// @Ensures r = 64 And s = 0
func Length() (r, s int) {
	var buf [64]byte
	var none [0]int
	return len(buf), len(none)
}

// @Ensures r = 64 And s = 0
func LengthBoxed() (r, s int) {
	var buf [64]byte
	var none [0]int
	_ = peek(buf[:])
	_ = peekInts(none[:])
	return len(buf), len(none)
}

// Flags holds booleans.
//
// @Ensures r And ~s
func Flags() (r, s bool) {
	var seen [3]bool
	seen[1] = true
	return seen[1], seen[2]
}

// @Ensures r = |p|
func peekBools(p []bool) (r int) { return len(p) }

// @Ensures r And ~s
func FlagsBoxed() (r, s bool) {
	var seen [3]bool
	seen[1] = true
	_ = peekBools(seen[:])
	return seen[1], seen[2]
}
