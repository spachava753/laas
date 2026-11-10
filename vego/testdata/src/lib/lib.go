// Package lib holds verified functions that another package calls.
package lib

import "errors"

//@ Predicate sorted(A) ::= Forall i in [0, |A|) : Forall j in [i, |A|) : A[i] <= A[j]

var errEmpty = errors.New("empty")

// Smallest returns the first element of a sorted slice, which is its least.
//
// @ Requires sorted(A) And |A| > 0
func Smallest(A []int) (least int) {
	return A[0]
}

//@ Ensures A[0:|A|) >= least And least = A[0]

// Clear overwrites the slice with zeros.
func Clear(A []int) {
	//@ Invariant A[0:i) = 0
	for i := range A {
		A[i] = 0
	}
}

//@ Ensures A'[0:|A|) = 0

// Head returns the first element, or an error for an empty slice.
func Head(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, errEmpty
	}
	return A[0], nil
}

//@ Ensures err = nil <-> |A| > 0
//@ Ensures err = nil -> first = A[0]

// Broken has a contract its body does not meet.
func Broken(x int) (y int) {
	return x // want `postcondition may not hold: y > x`
}

//@ Ensures y > x

// Unannotated is exported but not verified.
func Unannotated(x int) int { return x }

// Wrap relies on Broken, whose proof failed, so its own contract is not
// established either, although nothing is wrong inside it.
func Wrap(x int) (y int) {
	return Broken(x)
}

//@ Ensures y > x

const limit = 1

// SafeDivide uses a constant of this package in its contract.
//
// @ Requires d >= limit And n >= 0
func SafeDivide(n, d int) (q int) {
	return n / d
}

//@ Ensures q <= n
