package trialfaults

import "flag"

// The messages that misled the trial, each with what it says now.

// @Requires |dst| >= |src|
// @Modifies dst
// @Ensures True
func Copies(dst, src []byte) {
	copy(dst, src) // want `cannot verify Copies: the built-in function copy is not supported yet; write the copy as a loop that assigns each element, or, when the source is no longer than the destination, as dst = append\(dst\[:0\], src...\)`
}

// encoder holds an array.
type encoder struct {
	n   int
	out [4]byte
}

// @Requires e != nil
// @Ensures True
func Encodes(e *encoder) { // want `cannot verify Encodes: parameter e has unsupported type \*trialfaults.encoder; trialfaults.encoder holds an array in field out, and arrays are not supported yet`
}

// inner holds an array two structs down.
type inner struct{ buf [2]int }

type outer struct{ in inner }

// @Ensures True
func Nested(o outer) { // want `outer holds an array in field in.buf`
}

func usage() {}

// @Ensures True
func SetsUsage() {
	flag.Usage = usage // want `cannot verify SetsUsage: flag.Usage is a package-level variable of package flag, and assigning one is not supported yet`
}

type lazybuf struct{ s string }

// The suggestion is the function's own signature, with names that shadow
// nothing: b is the receiver, and n a package-level variable the body
// reads. A field after a dot shadows nothing.
var n = 5

// @Requires b != nil
// @Ensures True
func (b *lazybuf) string() string { // want `string has annotations, so each of its results needs a name, as in func \(b \*lazybuf\) string\(\) \(s string\)`
	return b.s
}

// @Ensures True
func count() int { // want `count has annotations, so each of its results needs a name, as in func count\(\) \(i int\)`
	return n
}

// @Ensures True
func number() int { // want `number has annotations, so each of its results needs a name, as in func number\(\) \(i1 int\)`
	i := n
	return i
}

// The receiver's name is taken.
type intBox struct{ v int }

// @Ensures True
func (i intBox) get() int { // want `get has annotations, so each of its results needs a name, as in func \(i intBox\) get\(\) \(i1 int\)`
	return i.v
}

// @Ensures True
func pair(x int) (int, error) { // want `pair has annotations, so each of its results needs a name, as in func pair\(x int\) \(i int, err error\)`
	return x, nil
}

// An annotation's names count too: e names an error variable here, so the
// error is not called e; err names nothing, and is the name the contract
// means.
var e error

// @Ensures err = e Or err = nil
func failing() error { // want `failing has annotations, so each of its results needs a name, as in func failing\(\) \(err error\)`
	return nil
}

// entry is a type whose suggested name, e, is taken by the error variable
// the contract names.
type entry struct{ k int }

// @Ensures e = nil Or True
func lookupEntry() entry { // want `lookupEntry has annotations, so each of its results needs a name, as in func lookupEntry\(\) \(e1 entry\)`
	return entry{}
}

// num is a type whose suggested name, n, is the package-level variable
// the body reads, which the name would hide.
type num int

// @Ensures True
func numbered() num { // want `numbered has annotations, so each of its results needs a name, as in func numbered\(\) \(n1 num\)`
	return num(n)
}

// grow appends x.
//
// @Requires |s| < 1000000
// @Modifies s
// @Ensures |result| = |s| + 1
// @Ensures fresh(result) Or within(result, s)
func grow(s []int, x int) (result []int) {
	return append(s, x)
}

// A result cannot be listed in Modifies, so the message does not ask for it.
//
// @Requires |A| <= 1000
// @Ensures True
func ThroughGrow(A []int) (out []int) {
	// @Invariant |out| <= i
	for i := range A {
		out = grow(out, A[i]) // want `grow may modify out, which ThroughGrow may not modify; out is a result, and a // @Modifies clause names memory only by a path from a parameter: if what out refers to may be memory of the caller, list it by the parameter it comes from; if it is memory that ThroughGrow made, nothing here shows that, since a loop that assigns out the result of a call forgets where its memory came from: append to it in the loop itself`
	}
	return out
}
