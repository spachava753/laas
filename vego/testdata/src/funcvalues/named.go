package funcvalues

import (
	"funcvalueslib"
	"strconv"
)

// A function, or a method of a value, can be used as a value of a function
// type with a contract. It is checked against the contract where it is used,
// as a function of its own that calls it.

// double doubles a number in range.
//
// @Requires 0 <= x <= 1000
// @Ensures y = 2 * x
func double(x int) (y int) {
	return 2 * x
}

// DoubleAll maps a slice with double.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 1000
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : 0 <= xs'[i] <= 2000
func DoubleAll(xs []int) {
	Apply(xs, double)
}

// Doubler returns double as a mapper.
//
// @Ensures f != nil
func Doubler() (f Mapper) {
	return double
}

// Counter counts one up.
//
// @Requires 0 <= n < 1000
// @Ensures m = n + 1
type Counter func(n int) (m int)

// CountOf uses a function of another package as a value.
//
// @Ensures c != nil
func CountOf() (c Counter) {
	var counter Counter = funcvalueslib.Count
	return counter
}

// Show shows a number.
//
// @Ensures True
type Show func(n int) (s string)

// ShowOf uses a trusted function as a value.
//
// @Ensures s != nil
func ShowOf() (s Show) {
	return strconv.Itoa
}

// Scale multiplies by a factor it holds.
type Scale struct{ k int }

// By multiplies by the factor of the scale.
//
// @Requires 0 <= x <= 1000 And 0 <= p.k <= 2
// @Ensures y = p.k * x
func (p Scale) By(x int) (y int) {
	return p.k * x
}

// ScaleBy uses a method of a scale as a mapper. The receiver is copied
// where the method value is made, and what is known of it there is known
// when the mapper runs.
//
// @Requires 0 <= k <= 2
// @Ensures f != nil
func ScaleBy(k int) (f Mapper) {
	s := Scale{k: k}
	return s.By
}

// Pair takes two numbers, the second never zero.
//
// @Requires y != 0
// @Ensures True
type Pair func(x int, y int) (z int)

// divideBySecond divides by its second parameter.
//
// @Requires x != 0
// @Ensures True
func divideBySecond(y, x int) (z int) {
	return 100 / x
}

// Positional uses a function whose parameters are named the other way round:
// its second parameter is the second of the type, whatever their names.
//
// @Ensures p != nil
func Positional() (p Pair) {
	return divideBySecond
}
