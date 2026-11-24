// Package typederrors holds errors of the project's own types: values of
// concrete types converted to error, and what == says of them (F33).
package typederrors

import "errors"

// Error is a named integer error, as strconv's.
type Error int

// @Ensures True
func (e Error) Error() (s string) { return "error" }

const (
	ErrRange  Error = 1
	ErrSyntax Error = 2
)

// PE is a struct error used through a pointer.
type PE struct{ Line int }

// @Ensures True
func (e *PE) Error() (s string) { return "pe" }

// Other has the underlying type of Error, and is another type.
type Other int

// @Ensures True
func (e Other) Error() (s string) { return "other" }

// SErr is a string error, which is not one integer, so each conversion is
// an error of its own that == compares by its bytes.
type SErr string

// @Ensures True
func (e SErr) Error() (s string) { return string(e) }

// Pair is a struct error held by value.
type Pair struct{ A, B int }

// @Ensures True
func (p Pair) Error() (s string) { return "pair" }

// Alias is the same type as Error.
type Alias = Error

// @Ensures err != nil
func Ret() (err error) { // want `the contract of Ret may also be met by a function that always returns an error`
	return ErrSyntax
}

// @Ensures r
func Same() (r bool) {
	var a error = ErrSyntax
	var b error = Error(2)
	return a == b
}

// @Ensures r
func SameThroughAlias() (r bool) {
	var a error = Alias(2)
	return a == ErrSyntax
}

// @Ensures ~r
func Differ() (r bool) {
	var a error = ErrSyntax
	return a == ErrRange
}

// @Ensures ~r
func DifferTypes() (r bool) {
	var a error = Other(2)
	return a == ErrSyntax
}

// @Ensures ~r
func MadeDiffers() (r bool) {
	a := errors.New("x")
	return a == ErrSyntax
}

// MadeAfter makes the error after the conversion, so what a made error
// holds is stated when it is made.
//
// @Ensures ~r
func MadeAfter() (r bool) {
	var b error = ErrSyntax
	a := errors.New("x")
	return a == b
}

// NilPointers holds two nil pointers of one type, which Go's == calls
// equal whatever position the logic gives them (F2 of the design review).
//
// @Requires p = nil
// @Ensures r
func NilPointers(p *PE) (r bool) {
	var a error = p
	var b error = (*PE)(nil)
	return a == b
}

// @Ensures r
func SamePointer(p *PE) (r bool) {
	var a error = p
	var b error = p
	return a == b
}

// @Requires p != q
// @Ensures ~r
func OtherPointer(p, q *PE) (r bool) {
	var a error = p
	var b error = q
	return a == b
}

// @Ensures r
func Strings(s string) (r bool) {
	var a error = SErr(s)
	var b error = SErr(s)
	return a == b
}

// @Ensures ~r
func StringsDiffer() (r bool) {
	var a error = SErr("a")
	return a == SErr("b")
}

// @Ensures r <-> a = c
func Pairs(a, c int) (r bool) {
	var x error = Pair{a, 1}
	var y error = Pair{c, 1}
	return x == y
}

// @Ensures r <-> n = 2
func Switch(n int) (r bool) {
	var e error = Error(n)
	switch e {
	case ErrRange:
		return false
	case ErrSyntax:
		return true
	}
	return false
}

// @Ensures err != nil
func NilPointerIsNotNil() (err error) { // want `the contract of NilPointerIsNotNil may also be met by a function that always returns an error`
	var p *PE
	return p
}

// @Ensures False
func NotDifferent(n int) (r bool) {
	var a error = Error(n)
	var b error = Error(n)
	return a != b // want `postcondition may not hold: False`
}

// @Ensures False
func NotSame(n, m int) (r bool) {
	var a error = Error(n)
	var b error = Error(m)
	return a == b // want `postcondition may not hold: False`
}

// NotContradictory converts equal integers of two types: the two errors
// differ, and nothing makes the facts contradict each other.
//
// @Ensures False
func NotContradictory(n int) (r bool) {
	var a error = Other(n)
	var b error = Error(n)
	return a != b // want `postcondition may not hold: False`
}
