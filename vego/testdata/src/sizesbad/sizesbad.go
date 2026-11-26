// Package sizesbad holds what a declared memory does not make provable
// (F38): sizes that a number gives, products of lengths, the forms that
// reserve memory nothing writes, a precondition that the declaration
// contradicts, and a Variant that rests on the bounds of lengths.
package sizesbad

import (
	"bytes"
	"io"
	"strings"
)

// @Requires n >= 0
// @Ensures True
func Made(n int) (r []byte) {
	r = make([]byte, n) // want `vego: the slice made may be more than can be allocated`
	return r
}

// @Requires n >= 0
// @Ensures True
func Repeated(s string, n int) (r string) {
	r = strings.Repeat(s, n) // want `vego: precondition of Repeat may not hold: \|s\| \* count <= MaxAlloc`
	return r
}

// @Ensures True
func Joined(xs []string) (r string) {
	r = strings.Join(xs, ", ") // want `vego: precondition of Join may not hold: Forall i in \[0, \|elems\|\) : \|elems\| \* \(\|elems\[i\]\| \+ \|sep\| \+ 1\) <= MaxInt` `vego: precondition of Join may not hold: Forall i in \[0, \|elems\|\) : \|elems\| \* \(\|elems\[i\]\| \+ \|sep\| \+ 1\) <= MaxAlloc`
	return r
}

// @Ensures True
func Replaced(s, old, new string) (r string) {
	r = strings.ReplaceAll(s, old, new) // want `vego: precondition of ReplaceAll may not hold: \|s\| \+ \(\|s\| \+ 1\) \* \|new\| <= MaxInt` `vego: precondition of ReplaceAll may not hold: \|s\| \+ \(\|s\| \+ 1\) \* \|new\| <= MaxAlloc`
	return r
}

// The make of a spread append never exists, so its length is a number.
// @Requires 0 <= n And n <= MaxAlloc
// @Modifies s
// @Ensures True
func Extended(s []byte, n int) (r []byte) {
	r = append(s, make([]byte, n)...) // want `vego: the slice that append grows may be more than can be allocated`
	return r
}

// @Requires 0 <= n And n <= MaxAlloc
// @Modifies s
// @Ensures True
func ExtendedParens(s []byte, n int) (r []byte) {
	r = append(s, (make([]byte, n))...) // want `vego: the slice that append grows may be more than can be allocated`
	return r
}

// A length times a number from the input is a number.
// @Requires 0 <= k And k <= 1000000
// @Ensures True
func Scaled(s string, k int) (r []byte) {
	r = make([]byte, len(s)*k) // want `vego: multiplication may overflow int` `vego: the slice made may be more than can be allocated`
	return r
}

// A precondition that asks for a slice longer than the declaration allows.
// @Requires |s| = MaxAlloc And cap(s) = |s|
// @Modifies s
// @Ensures True
func AtTheLimit(s []byte) (r []byte) {
	r = append(s, 1) // want `vego: what is known here contradicts the declared memory: a string, the entries of a map, or the array of a slice here would be larger than the declaration allows`
	return r
}

// A loop that grows a slice without end, ended in a Variant by the bound
// on lengths.
// @Ensures True
func GrowsForever() (r []byte) {
	// @Variant MaxAlloc - |r|
	for { // want `vego: loop variant may be negative: MaxAlloc - \|r\|; it holds only because a map cannot have more keys, and a string or the array of a slice cannot be longer, than memory can hold`
		r = append(r, 1)
	}
}

// @Ensures True
func ConcatenatesForever() (r string) {
	// @Variant MaxInt - |r|
	for { // want `vego: loop variant may be negative: MaxInt - \|r\|; it holds only because`
		r = r + "a"
	}
}

// @Ensures True
func ByInvariant() (r []byte) {
	// @Invariant |r| <= MaxAlloc
	// @Variant MaxAlloc - |r|
	for { // want `vego: loop invariant may not be preserved: \|r\| <= MaxAlloc; it holds only because`
		r = append(r, 1)
	}
}

// An int that overflows is not a length.
// @Ensures True
func Squared(s string) (r int) {
	r = len(s) * len(s) // want `vego: multiplication may overflow int`
	return r
}

// @Ensures True
func Writer(w io.Writer) {}

// A buffer as an io.Writer is still refused, for what it owns.
// @Ensures True
func Buffered() {
	var b bytes.Buffer
	Writer(&b) // want `vego: cannot verify Buffered: converting a value of type \*bytes.Buffer to io.Writer is not supported yet: \*bytes.Buffer owns memory`
}

// A bound that a contract states for its own reasons is still owed by the
// caller.
// @Requires |s| <= 100
// @Ensures True
func Short(s string) (r string) {
	r = s + "."
	return r
}

// @Ensures True
func CallsShort(s string) (r string) {
	r = Short(s) // want `vego: precondition of Short may not hold: \|s\| <= 100`
	return r
}

// A bound that a contract writes with MaxAlloc bounds a number; the
// declaration does not make it smaller (F2 of the design review).
// @Requires 0 <= n And n <= MaxAlloc
// @Ensures True
func Reserves(n int) (r []int64) {
	r = make([]int64, n) // want `vego: the slice made may be more than can be allocated`
	return r
}

// What only the declaration proved of an append is not assumed after it.
// @Requires cap(s) = |s|
// @Modifies s
// @Ensures True
func Leaks(s []byte) (r []byte) {
	r = append(s, 1)
	// @Assert 2 * |r| + 65536 <= MaxAlloc // want `vego: assertion may not hold: 2 \* \|r\| \+ 65536 <= MaxAlloc`
	return r
}

// The made slice of a spread append never exists, so a length of data
// that it is made with does not bound what the append reserves unwritten.
// @Modifies s
// @Ensures True
func ExtendedByLength(s, t []byte) (r []byte) {
	r = append(s, make([]byte, len(t))...) // want `vego: the slice that append grows may be more than can be allocated`
	return r
}

// A recursive precondition that only the declaration would prove gives a
// Variant nothing (F18 of the review of step 2a).
// @Requires 2 * |s| + 65536 <= MaxAlloc
// @Modifies s
// @Variant MaxAlloc - |s|
// @Ensures True
func GrowsForeverByRecursion(s []byte) (r []byte) {
	s = append(s, 0)
	return GrowsForeverByRecursion(s) // want `vego: precondition of GrowsForeverByRecursion may not hold: 2 \* \|s\| \+ 65536 <= MaxAlloc`
}

// A bound between the memory and four times it: what the array of a slice
// may take is R, not M (F19 of the review of step 2a).
// @Requires 300 * |p| + 65536 <= MaxAlloc
// @Ensures True
func Big(p []byte) (r []byte) {
	r = make([]byte, 300*len(p))
	return r
}

// @Ensures True
func HandsBig(p []byte) (r []byte) {
	r = Big(p) // want `vego: precondition of Big may not hold: 300 \* \|p\| \+ 65536 <= MaxAlloc`
	return r
}
