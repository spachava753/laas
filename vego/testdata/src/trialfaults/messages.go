package trialfaults

import "flag"

// The messages that misled the trial, each with what it says now.

// @Requires |dst| >= |src|
// @Modifies dst
// @Ensures True
func Copies(dst, src []string) {
	copy(dst, src) // want `cannot verify Copies: copy of a slice of string is not supported yet; copy is supported for slices of numbers and booleans, and from a string into a \[\]byte; write the copy as a loop that assigns each element`
}

// encoder holds an array of strings, which a struct cannot hold yet.
type encoder struct {
	n   int
	out [4]string
}

// @Requires e != nil
// @Ensures True
func Encodes(e *encoder) { // want `cannot verify Encodes: parameter e has unsupported type \*trialfaults.encoder; trialfaults.encoder holds an array of string in field out, and arrays in structs are supported only for elements that are numbers or booleans yet`
}

// inner holds an array of elements of size zero two structs down.
type inner struct{ buf [2]struct{} }

type outer struct {
	in inner
	n  int
}

// @Ensures True
func Nested(o outer) { // want `outer holds an array of struct\{\} in field in.buf, whose elements take no bytes, and an array in a struct cannot have elements of size zero`
}

func usage() {}

// @Ensures True
func SetsUsage() {
	flag.Usage = usage // want `cannot verify SetsUsage: flag.Usage is a variable of package flag that holds code, and code of this package stored there would be run by that package at times no contract describes; keeping code to run later is not supported yet`
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
		out = grow(out, A[i]) // want `grow may modify out, which ThroughGrow may not modify; out is a result, and a // @Modifies clause names memory only by a path from a parameter: if what out refers to may be memory of the caller, list it by the parameter it comes from; if it is memory that ThroughGrow made, nothing here shows that, since a loop that assigns out forgets where its memory came from: say so with // @Invariant fresh\(out\) on the loop`
	}
	return out
}

// @Ensures True
func Digest(hash [4]string) { // want `cannot verify Digest: parameter hash has unsupported type \[4\]string; \[4\]string is an array of string, and only arrays of numbers and booleans are supported yet; use a slice of string instead`
}

// set writes the first element.
//
// @Requires |s| > 0
// @Modifies s
// @Ensures True
func set(s []int) {
	s[0] = 1
}

// mk returns a slice that it does not say is new.
//
// @Ensures |r| = 3
func mk() (r []int) {
	return make([]int, 3)
}

// The advice says where the memory came from.
//
// @Ensures True
func FromCall() (n int) {
	tmp := mk()
	set(tmp) // want `set may modify tmp, which FromCall may not modify; it is memory that mk returned, and its contract does not say that this is new memory, so it may have existed when FromCall was called; if it is new, say so in the contract of mk, with // @Ensures fresh\(r\), or take it as a parameter and list it in a // @Modifies clause`
	return 0
}

// Point and Segment are structs.
type Point struct{ X, Y int }

type Segment struct{ From, To Point }

// The advice names the path from the parameter.
//
// @Requires s != nil
// @Ensures True
func Through(s *Segment) {
	p := &s.To
	p.X = 7 // want `p.X is assigned, which Through may not modify; list it in a // @Modifies clause, as s.To.X`
}

// Which is what this lists.
//
// @Requires s != nil
// @Modifies s.To.X
// @Ensures True
func Listed(s *Segment) {
	p := &s.To
	p.X = 7
}

// MakesPoint is a function type whose result its contract does not say is
// new.
//
// @Ensures p != nil
type MakesPoint func() (p *Point)

// @Requires m != nil
// @Ensures True
func FromValue(m MakesPoint) {
	p := m()
	p.X = 1 // want `p.X is assigned, which FromValue may not modify; it is memory that a call of m returned, and the contract of MakesPoint does not say that this is new memory, so it may have existed when FromValue was called; if it is new, say so in the contract of MakesPoint, with // @Ensures fresh\(p\), or take it as a parameter and list it in a // @Modifies clause`
}

// PointSource has a method whose result its contract does not say is new.
type PointSource interface {
	// @Ensures p != nil
	Get() (p *Point)
}

// @Requires s != nil
// @Ensures True
func FromMethod(s PointSource) {
	p := s.Get()
	p.X = 1 // want `p.X is assigned, which FromMethod may not modify; it is memory that a call of s.Get returned, and the contract of PointSource.Get does not say that this is new memory`
}

// FreshPoint says it is new, and the write is the function's own.
//
// @Ensures p != nil And fresh(p)
type FreshPoint func() (p *Point)

// @Requires m != nil
// @Ensures True
func FromFresh(m FreshPoint) {
	p := m()
	p.X = 1
}
