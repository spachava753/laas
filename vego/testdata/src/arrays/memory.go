package arrays

import (
	"crypto/md5"
	"crypto/sha256"
	"encoding/hex"
	"io"
	"strconv"
)

// put writes c at the start of p.
//
// @Requires |p| > 0
// @Modifies p
// @Ensures p'[0] = c
func put(p []byte, c byte) { p[0] = c }

// What a callee writes through a slice of an array is seen through the
// array, and what the array is written is seen through the slice.
//
// @Ensures r = 7 And s = 8
func ThroughSlice() (r, s byte) {
	var buf [4]byte
	put(buf[1:], 7)
	t := buf[:]
	buf[3] = 8
	return buf[1], t[3]
}

// Two slices of one array that overlap, written in turn.
//
// @Ensures r = 2 And s = 2
func Overlap() (r, s byte) {
	var buf [4]byte
	a, b := buf[0:3], buf[1:4]
	a[1] = 1
	b[0] = 2
	return a[1], buf[1]
}

// A copy taken after a slice of the array is made keeps the old value
// when the slice is written.
//
// @Ensures r = 0 And s = 9
func CopyKeeps() (r, s byte) {
	var a [2]byte
	t := a[:]
	b := a
	t[0] = 9
	return b[0], a[0]
}

// Capacity is the rest of the array, so an append writes it in place
// until it is full.
//
// @Ensures r = 5 And s = 4
func AppendInPlace() (r byte, s int) {
	var buf [4]byte
	t := append(buf[:1], 5)
	return buf[1], cap(t)
}

// An append past the end of the array moves, and leaves the array.
//
// @Ensures r = 0 And s = 5
func AppendMoves() (r byte, s int) {
	var buf [4]byte
	t := append(buf[:], 5)
	return buf[0], len(t)
}

// Read fills an array from a reader.
//
// @Requires r != nil
// @Modifies r
// @Ensures 0 <= n <= 64
func Read(r io.Reader) (n int, err error) {
	var buf [64]byte
	return r.Read(buf[:])
}

// Itoa formats into an array on the stack.
//
// @Ensures True
func Itoa(x int64) (s string) {
	var buf [24]byte
	return string(strconv.AppendInt(buf[:0], x, 10))
}

// Digest hashes data and prints the hash, as the trial's digest does.
//
// @Ensures |result| = 64
func Digest(data []byte) (result string) {
	hash := sha256.Sum256(data)
	return hex.EncodeToString(hash[:])
}

// @Ensures |result| = 32
func DigestMD5(data []byte) (result string) {
	hash := md5.Sum(data)
	return hex.EncodeToString(hash[:])
}

// Convert copies the first elements of a slice into an array.
//
// @Requires |p| >= 4
// @Ensures r[0] = p[0] And r[3] = p[3]
func Convert(p []byte) (r [4]byte) {
	return [4]byte(p)
}

// Returned is a slice of a local array, which Go moves to the heap.
//
// @Ensures |r| = 4 And r[0] = 1 And fresh(r)
func Returned() (r []byte) {
	var buf [4]byte
	buf[0] = 1
	return buf[:]
}

// Named results that a slice reaches are read after the deferred calls.
//
// @Ensures r[0] = 1
func DeferredWrite() (r [4]int) {
	s := r[:]
	defer func() { s[0] = 1 }()
	return r
}

// keep reads its argument.
//
// @Ensures r = a[0]
func keep(a [2]int) (r int) { return a[0] }

// A deferred call gets its argument as it was at the defer statement.
//
// @Ensures True
func DeferredArgument() {
	var a [2]int
	t := a[:]
	defer keep(a)
	t[0] = 5
}

// A function literal that writes an element assigns the array.
//
// @Ensures r = 4
func Captured() (r int) {
	var a [2]int
	set := func() { a[1] = 4 }
	set()
	return a[1]
}

// The range expression is evaluated when it has a call.
//
// @Ensures r = 4
func RangeCall() (r int) {
	// @Invariant 0 <= i <= 4
	// @Invariant r = i
	for i := range Make() {
		_ = i
		r++
	}
	return r
}

// A slice of an array of length zero is not nil.
//
// @Ensures r
func ZeroSlice() (r bool) {
	var z [0]byte
	return z[:] != nil
}
