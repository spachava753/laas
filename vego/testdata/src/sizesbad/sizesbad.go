// Package sizesbad holds what a declared memory does not make provable
// (F38): sizes that a number gives, products of lengths, the forms that
// reserve memory nothing writes, a precondition that the declaration
// contradicts, and a Variant that rests on the bounds of lengths.
package sizesbad

import (
	"bytes"
	"io"
	"slices"
	"strings"
)

// @Requires n >= 0
// @Ensures True
func Made(n int) (r []byte) {
	r = make([]byte, n) // want `vego: the slice made may reserve more than the declared memory allows a value to`
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

// The make of a spread append never exists, so its length is a number,
// held against the memory itself.
// @Requires 0 <= n And n <= MaxAlloc
// @Modifies s
// @Ensures True
func Extended(s []byte, n int) (r []byte) {
	r = append(s, make([]byte, n)...) // want `vego: the slice made may reserve more than the declared memory allows a value to` `vego: what append adds from make may reserve more than the declared memory allows: 256GB, the memory declared`
	return r
}

// @Requires 0 <= n And n <= MaxAlloc
// @Modifies s
// @Ensures True
func ExtendedParens(s []byte, n int) (r []byte) {
	r = append(s, (make([]byte, n))...) // want `vego: the slice made may reserve more than the declared memory allows a value to` `vego: what append adds from make may reserve more than the declared memory allows: 256GB, the memory declared`
	return r
}

// A length times a number from the input is a number.
// @Requires 0 <= k And k <= 1000000
// @Ensures True
func Scaled(s string, k int) (r []byte) {
	r = make([]byte, len(s)*k) // want `vego: multiplication may overflow int` `vego: the slice made may reserve more than the declared memory allows a value to`
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
	r = make([]int64, n) // want `vego: the slice made may reserve more than the declared memory allows a value to`
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
	r = append(s, make([]byte, len(t))...) // want `vego: what append adds from make may reserve more than the declared memory allows: 256GB, the memory declared`
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
	r = p
	return r
}

// @Ensures True
func HandsBig(p []byte) (r []byte) {
	r = Big(p) // want `vego: precondition of Big may not hold: 300 \* \|p\| \+ 65536 <= MaxAlloc`
	return r
}

// What a make reserves by a number is held against the bound on arrays
// (class N of the bound on every value): below MaxAlloc is not enough.
// @Requires 0 <= n And n <= 70368744177664
// @Ensures True
func MadeBelowMaxAlloc(n int) (r []byte) {
	r = make([]byte, n) // want `vego: the slice made may reserve more than the declared memory allows a value to: at most 1280000065536 bytes`
	return r
}

// Eight bytes for each byte of a string is more than an array may take.
// @Ensures True
func MadeEightFold(s string) (r []int64) {
	r = make([]int64, len(s)) // want `vego: the slice made may reserve more than the declared memory allows a value to`
	return r
}

// @Requires 0 <= n And n <= 1000
// @Modifies s
// @Ensures True
func ExtendedSmall(s []byte, n int) (r []byte) {
	r = append(s, make([]byte, n)...)
	return r
}

// @Requires 0 <= n And n <= 1099511627776
// @Ensures True
func GrowsBuilder(n int) (r string) {
	var b strings.Builder
	b.Grow(n) // want `vego: precondition of Grow may not hold under the declared memory: n <= Memory`
	r = b.String()
	return r
}

// @Requires 0 <= n And n <= 1099511627776
// @Ensures True
func GrowsSlice(s []byte, n int) (r []byte) {
	r = slices.Grow(s, n) // want `vego: precondition of Grow may not hold under the declared memory: n \* elemsize\(s\) <= Memory`
	return r
}

// A value whose type reserves more than an array may take.
type Holder struct {
	B [2000000000000]byte
}

// @Ensures r != nil
func NewHolder() (r *Holder) { // want `vego: cannot verify NewHolder: Holder is 2000000000000 bytes, more than the declared memory allows a value to reserve`
	return &Holder{}
}

// What an initialiser reserves is checked like any other (F12).
var reserved = make([]byte, 1<<45) // want `vego: the slice made may reserve more than the declared memory allows a value to`

// @Ensures r >= 0
func Reserved() (r int) {
	return len(reserved)
}

var grown = slices.Grow([]byte(nil), 1<<45) // want `vego: precondition of Grow may not hold under the declared memory: n \* elemsize\(s\) <= Memory`

// @Ensures r >= 0
func Grown() (r int) {
	return cap(grown)
}

// Two lengths may be the same string twice, so their sum is not bounded
// by the memory (F20 of the review of step 2c); bound it, or grow by each.
// @Ensures True
func GrowsForTwo(a, b string) (r string) {
	var w strings.Builder
	w.Grow(len(a) + len(b)) // want `vego: precondition of Grow may not hold under the declared memory: n <= Memory`
	w.WriteString(a)
	w.WriteString(b)
	r = w.String()
	return r
}

// A declared clause not proved is reported alone: it implies the size
// conjuncts of its entry, whose hint would not meet the declaration (F22
// of the review of step 2c).
// @Requires n >= 0
// @Ensures True
func GrowsAnyBuilder(n int) (r string) {
	var b strings.Builder
	b.Grow(n) // want `vego: precondition of Grow may not hold under the declared memory: n <= Memory`
	r = b.String()
	return r
}

// @Requires n >= 0
// @Ensures True
func GrowsAnySlice(s []byte, n int) (r []byte) {
	r = slices.Grow(s, n) // want `vego: precondition of Grow may not hold under the declared memory: n \* elemsize\(s\) <= Memory`
	return r
}
