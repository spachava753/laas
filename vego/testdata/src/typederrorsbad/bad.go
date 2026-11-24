// Package typederrorsbad holds formulas about typed errors that are
// refused or not proved. Its annotations draw reports, so the package
// hands none of its contracts to others, which is why it is apart from
// typederrors (S2 of F33).
package typederrorsbad

import "typederrors"

// Error is an integer error.
type Error int

// @Ensures True
func (e Error) Error() (s string) { return "error" }

// ErrSyntax is a constant error.
const ErrSyntax Error = 2

// InvalidByteError is a byte error.
type InvalidByteError byte

// @Ensures True
func (e InvalidByteError) Error() (s string) { return "invalid byte" }

// FErr is a float error.
type FErr float64

// @Ensures True
func (e FErr) Error() (s string) { return "f" }

// Empty has size zero.
type Empty struct{}

// @Ensures True
func (e *Empty) Error() (s string) { return "empty" }

// Other is an error and the name of a predicate.
type Other int

// @Ensures True
func (e Other) Error() (s string) { return "other" }

var _ = typederrors.ErrSyntax

// @Ensures err.(Error) = 300
func NotThreeHundred() (err error) {
	return ErrSyntax // want `postcondition may not hold: err.\(Error\) = 300`
}

// @Ensures err = InvalidByteError(300) // want `InvalidByteError\(300\): 300 is not a value of InvalidByteError`
func OutOfRange() (err error) {
	return nil
}

// @Ensures err = InvalidByteError(n) // want `InvalidByteError\(...\) of a value of type int, which may not fit InvalidByteError`
func WiderValue(n int) (err error) {
	return nil
}

// @Ensures err = 5 // want `cannot compare err \(error\) with 5 \(int\)`
func Untyped() (err error) {
	return nil
}

// @Ensures err = FErr(1) // want `FErr\(...\) converts to a type whose values are not integers, strings, or booleans`
func FloatError() (err error) {
	return nil
}

// @Ensures err = Other{1, 2} // want `syntax error in Ensures annotation: unexpected character`
func StructError() (err error) {
	return nil
}

// @Ensures holds(err, Undefined) // want `Undefined is not a type here`
func UnknownType() (err error) {
	return nil
}

// @Predicate Other(x) ::= x > 0

// @Ensures err = Other(2) // want `Other is both a type and a predicate here; rename the predicate`
func TypeAndPredicate() (err error) {
	return nil
}

// @Ensures as(err, *Empty)
func AsInFormula() (err error) {
	return nil // want `postcondition may not hold: as\(err, \*Empty\)`
}

// Getter has a contract no value of its type can meet: what an error
// holds as an InvalidByteError is a byte (F8 of the design review).
type Getter interface {
	// @Ensures err.(InvalidByteError) = 300
	Get() (err error) // want `the contract of Getter.Get contradicts itself`
}

// Both has a contract that contradicts itself.
type Both interface {
	// @Ensures err = Error(1) And err = Error(2)
	Get() (err error) // want `the contract of Both.Get contradicts itself`
}

// Fine has a contract that a value can meet.
type Fine interface {
	// @Ensures err = nil Or err = ErrSyntax
	Get() (err error)
}

// @Requires g != nil
// @Ensures r -> e = ErrSyntax
func UseFine(g Fine) (r bool, e error) {
	err := g.Get()
	return err != nil, err
}

// @Ensures err = p // want `== on values of \*Empty is not identity, so an error cannot be compared with one in a formula`
func ZeroSizeFormula(p *Empty) (err error) {
	return nil
}

// TypedNilNotNil returns nil, which is not the error that holds a nil
// pointer: the nil of a formula beside a pointer is a nil pointer only as
// written.
//
// @Requires p = nil
// @Ensures err = p
func TypedNilNotNil(p *typederrors.PE) (err error) {
	return nil // want `postcondition may not hold: err = p`
}

// SErr is a string error.
type SErr string

// @Ensures True
func (e SErr) Error() (s string) { return string(e) }

// wrapRunes converts runes to a string error, which Go encodes as UTF-8:
// its entry reads the runes as bytes, which a formula refuses (F16 of the
// review of S2).
func wrapRunes(rs []rune) (err error) { return SErr(rs) }

// @Ensures ~r
func Accent() (r bool) {
	err := wrapRunes([]rune{233}) // want `the trusted contract of typederrorsbad.wrapRunes \(trusted.yaml:\d+\) cannot be used: .*SErr\(...\) converts a string or a \[\]byte`
	return err == SErr("é")
}

// B is a byte error.
type B byte

// @Ensures True
func (e B) Error() (s string) { return "b" }

func two() (err error) { return Error(1) }

func big() (err error) { return B(1) }

func wide(n int) (err error) { return InvalidByteError(n) }

// UsesTwo calls a trusted function whose entry contradicts itself.
//
// @Ensures True
func UsesTwo() (r bool) {
	return two() == nil // want `the trusted contract of typederrorsbad.two \(trusted.yaml:\d+\) cannot be used: .*contradicts itself`
}

// UsesBig calls a trusted function whose entry says what a byte error
// cannot hold.
//
// @Ensures True
func UsesBig() (r bool) {
	return big() == nil // want `the trusted contract of typederrorsbad.big \(trusted.yaml:\d+\) cannot be used: .*contradicts itself`
}

// UsesWide calls a trusted function whose entry converts an int to a
// byte error, which may not fit.
//
// @Ensures True
func UsesWide(n int) (r bool) {
	return wide(n) == nil // want `the trusted contract of typederrorsbad.wide \(trusted.yaml:\d+\) cannot be used: .*InvalidByteError\(...\) of a value of type int, which may not fit InvalidByteError`
}
