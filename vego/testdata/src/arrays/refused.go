package arrays

import (
	"errors"
	"fmt"
	"slices"
)

// The types and uses below are not supported yet, each with a message
// that names what is refused. A slice of arrays, and a function type or an
// interface with an array in its signature, are refused only where an
// element or a call is reached; holding them, as at the base, verifies.

// @Ensures r = |xs|
func Count(xs [][4]byte) (r int) { return len(xs) }

// @Requires |xs| > 0
// @Ensures |r| = |xs| - 1
func Tail(xs [][4]byte) (r [][4]byte) { return xs[1:] }

// @Ensures r = |m|
func Keys(m map[string][4]byte) (r int) { return len(m) }

type holder struct {
	hs [][32]byte
	n  int
}

// @Requires h != nil
// @Modifies h
// @Ensures h.n' = |h.hs|
func (h *holder) Fix() { h.n = len(h.hs) }

// @Ensures r <-> f != nil
func HasFunc(f func() [4]byte) (r bool) { return f != nil }

// Hasher returns a hash.
type Hasher interface{ Sum() [32]byte }

// @Ensures r <-> h != nil
func HasHasher(h Hasher) (r bool) { return h != nil }

// @Requires |xs| > 0
// @Ensures True
func FirstElement(xs [][4]byte) (r byte) {
	return xs[0][0] // want `cannot verify FirstElement: indexing a \[\]\[4\]byte is not supported`
}

// @Ensures True
func RangeElements(xs [][4]byte) (r int) {
	for _, x := range xs { // want `cannot verify RangeElements: slices of \[4\]byte are not supported`
		r = int(x[0])
	}
	return r
}

// @Ensures True
func AppendElement(xs [][4]byte) (r [][4]byte) {
	return append(xs, [4]byte{}) // want `cannot verify AppendElement: .*\[4\]byte`
}

// @Ensures True
func ContainsArray(xs [][4]byte, x [4]byte) (r bool) {
	return slices.Contains(xs, x) // want `the trusted contract of slices.Contains .*s has type \[4\]byte, which is not supported`
}

// HashFn has a contract, but its signature has an array.
//
// @Ensures True
type HashFn func(p []byte) (h [32]byte)

// @Requires f != nil
// @Ensures True
func CallHashFn(f HashFn) (r byte) {
	return f(nil)[0] // want `the contract of HashFn cannot be used: its signature takes or returns an array, and function types and methods of interfaces whose signatures hold arrays are not supported yet`
}

// @Ensures True
func ToAny() (r any) {
	return [2]int{1, 2} // want `cannot verify ToAny: converting a \[2\]int to any is not supported: an interface value or an error cannot hold an array yet`
}

// ArrayError is an error that is an array.
type ArrayError [2]int

// @Ensures True
func (a ArrayError) Error() (s string) { return "array" }

// @Ensures True
func ToError() (err error) {
	return ArrayError{1, 2} // want `cannot verify ToError: converting an ArrayError to an error is not supported: an interface value or an error cannot hold an array yet`
}

// @Requires x != nil
// @Ensures True
func Assert(x any) (r bool) {
	_, ok := x.([2]int) // want `cannot verify Assert: asserting an interface value to \[2\]int is not supported: an interface value or an error cannot hold an array yet`
	return ok
}

// @Requires x != nil
// @Ensures True
func Switch(x any) (r int) {
	switch x.(type) {
	case [2]int: // want `cannot verify Switch: a case of \[2\]int in a type switch is not supported: an interface value or an error cannot hold an array yet`
		return 1
	}
	return 0
}

// @Requires err != nil
// @Ensures True
func As(err error) (r bool) {
	var a ArrayError
	return errors.As(err, &a) // want `cannot verify As: errors.As with a target of ArrayError is not supported: an interface value or an error cannot hold an array yet`
}

// @Ensures r -> holds(x, ArrayError) // want `holds\(x, ArrayError\): ArrayError holds an array, and an interface value or an error cannot hold an array yet`
func Holds(x any) (r bool) { return false }

// @Ensures True
func Format(h [32]byte) (s string) {
	return fmt.Sprintf("%x", h) // want `cannot verify Format: Sprintf formats h, a value of type \[32\]byte, .*\[32\]byte is an array, which verified code cannot format yet; format a slice of it, as in a\[:\]`
}

// @Ensures True
func FormatSlice(h [32]byte) (s string) {
	return fmt.Sprintf("%x", h[:])
}

// @Ensures True
func MapKey(m map[[2]int]bool) (r bool) { // want `cannot verify MapKey: parameter m has unsupported type map\[\[2\]int\]bool`
	return m[[2]int{}]
}

// @Ensures True
func MapValue(m map[string][4]byte) (r byte) {
	return m["x"][0] // want `cannot verify MapValue: .*map\[string\]\[4\]byte`
}

// @Ensures True
func Pointer() (r int) {
	var buf [4]int
	p := &buf // want `cannot verify Pointer: p has unsupported type \*\[4\]int; \*\[4\]int points to an array, and pointers to arrays are not supported yet; use a slice of the array, as in a\[:\]`
	return p[0]
}

// @Ensures True
func Grid() (r int) {
	var g [4][4]int // want `cannot verify Grid: g has unsupported type \[4\]\[4\]int; \[4\]\[4\]int is an array of \[4\]int, and only arrays of numbers and booleans are supported yet; use one array of 16 elements indexed i\*4 \+ j, or a slice of slices, instead`
	return g[1][2]
}

// @Ensures True
func Names() (r string) {
	names := [2]string{"a", "b"} // want `cannot verify Names: names has unsupported type \[2\]string; \[2\]string is an array of string, and only arrays of numbers and booleans are supported yet; use a slice of string instead`
	return names[0]
}

type point struct{ x, y int }

// @Ensures True
func Points() (r int) {
	var ps [2]point // want `cannot verify Points: ps has unsupported type \[2\]arrays.point; \[2\]arrays.point is an array of arrays.point, and only arrays of numbers and booleans are supported yet; use a slice of arrays.point instead`
	return ps[0].x
}

// @Ensures True
func Huge() (r byte) {
	var b [1 << 49]byte // want `cannot verify Huge: \[562949953421312\]byte is 562949953421312 bytes, more than one allocation can be \(MaxAlloc, 281474976710656 bytes\), so no program can make it`
	return b[0]
}

// table is written, so it is not a value every function can read.
var table [4]int

// @Ensures True
func WriteTable() {
	table[0] = 1 // want `cannot verify WriteTable: table\[0\] is part of the package-level variable table, which a verified function cannot assign yet`
}

// @Ensures True
func ReadTable() (r int) {
	return table[1] // want `cannot verify ReadTable: table is assigned at refused.go:\d+; package-level arrays that are changed are not supported yet`
}

// A slice of *int can be read since F37, so the message offers one.
//
// @Ensures True
func Pointers() (r int) {
	var ps [2]*int // want `cannot verify Pointers: ps has unsupported type \[2\]\*int; \[2\]\*int is an array of \*int, and only arrays of numbers and booleans are supported yet; use a slice of \*int instead$`
	return len(ps)
}

// A switch on an array is not supported; == is.
//
// @Ensures True
func Switch2(a [2]int) (r int) {
	switch a { // want `cannot verify Switch2: a switch on an array of type \[2\]int is not supported yet; compare the array with == in an if`
	case [2]int{1, 2}:
		return 1
	}
	return 0
}
