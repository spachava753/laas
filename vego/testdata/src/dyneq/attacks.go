package dyneq

import "math"

// What is refused or not proved (S3 of F34).

// Two values of which nothing is known may hold one type on which ==
// panics.
//
// @Ensures True
func Eq(a, b any) (r bool) {
	return a == b // want `a == b may panic: a and b may hold values of one type on which == panics`
}

// @Requires holds(a, []int) And holds(b, []int)
// @Ensures True
func Slices(a, b any) (r bool) {
	return a == b // want `a == b may panic: a and b may hold values of one type on which == panics`
}

// A struct with a blank field of a slice type panics under ==.
type Blank struct {
	A int
	_ []int
}

// @Ensures True
func BlankSlice() (r bool) {
	x, y := any(Blank{A: 1}), any(Blank{A: 1})
	return x == y // want `x == y may panic`
}

// A value that holds an interface value beside one: == on it may panic.
type Holder struct{ X any }

// @Ensures True
func HolderEq(v any) (r bool) {
	return v == Holder{X: []int{}} // want `cannot verify HolderEq: comparing an interface value with a value of type Holder is not supported: == on two values of Holder may panic, since it holds an interface value`
}

// A float that is NaN is not equal to itself.
type F struct{ V float64 }

// @Ensures r
func NaN() (r bool) {
	x := any(F{V: math.NaN()})
	return x == x // want `postcondition may not hold: r`
}

// Two types, one value.
//
// @Ensures r
func IntAndInt64() (r bool) {
	return any(3) == any(int64(3)) // want `postcondition may not hold: r`
}

// @Ensures ~r
func IntAndInt64Honest() (r bool) {
	return any(3) == any(int64(3))
}

// Claims that say too much.
//
// @Ensures ~r
func SameThree() (r bool) {
	return any(3) == any(3) // want `postcondition may not hold: ~r`
}

// @Ensures r
func OtherFour() (r bool) {
	return any(3) == any(4) // want `postcondition may not hold: r`
}

// @Ensures r
func ParamIsThree(v any) (r bool) {
	return v == 3 // want `postcondition may not hold: r`
}

// @Ensures k = 1
func NameOfTwo() (k int) {
	return Name(2) // want `postcondition may not hold: k = 1`
}

// In a formula, = is identity of values, and its negation says nothing
// that code can observe (O4 of the design of F34).

// @Requires p != nil
// @Ensures a != b // want `in Ensures annotation: a != b between two interface values that are not nil is not supported`
func Differ(p *Circle) (a, b any) {
	return p, p
}

// @Requires p != nil
// @Ensures ~(a = b) // want `in Ensures annotation: ~\(a = b\) between two interface values that are not nil is not supported`
func NotSame(p *Circle) (a, b any) {
	return p, p
}

// = is still identity.
//
// @Ensures y = x
func Keep(x any) (y any) {
	return x
}

// What Go's == says is stated through what the values hold.
//
// @Requires holds(a, int) And holds(b, int)
// @Ensures r <-> (holds(a, int) And holds(b, int) And a.(int) = b.(int))
func GoEq(a, b any) (r bool) {
	return a == b
}

// An error whose type holds a float is not equal to itself when it holds
// a NaN, so two values made from it are not known to be equal.
type FloatErr struct{ V float64 }

// @Ensures True
func (e FloatErr) Error() (s string) { return "float" }

// @Ensures r
func NaNErr() (r bool) {
	var err error = FloatErr{V: math.NaN()}
	var a, b any = err, err
	return a == b // want `postcondition may not hold: r`
}

// The refusal names the operands as written (F20 of the review of S3).
//
// @Requires |xs| = 2
// @Ensures Forall i in [0, 2) : xs[i] != a // want `in Ensures annotation: xs\[i\] != a between two interface values that are not nil is not supported`
func NotAmong(xs []any) (a any) {
	return any(1)
}

// A negation that is not written directly on = still means that the
// values are not the same value, which two conversions are not.
//
// @Requires p != nil
// @Ensures (a = b) -> False
func TwoConversionsImply(p *Circle) (a, b any) {
	return p, p
}
