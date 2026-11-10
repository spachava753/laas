// Package client calls verified functions of package lib and relies on the
// contracts that package published.
package client

import "lib"

// The predicate of the same name here is a different one.
//
//@ Predicate sorted(A) ::= |A| = 2

// Least uses lib's contract, including lib's own notion of sorted.
//
// @ Requires |A| > 1 And Forall i in [0, |A|) : Forall j in [i, |A|) : A[i] <= A[j]
func Least(A []int) (least int) {
	return lib.Smallest(A)
}

//@ Ensures least <= A[1]

// LocalSorted satisfies this package's sorted, which is not lib's.
//
// @ Requires sorted(A)
func LocalSorted(A []int) int {
	return lib.Smallest(A) // want `precondition of Smallest may not hold: sorted\(A\)`
}

// Cleared knows that lib.Clear writes its argument and what it leaves.
//
// @ Requires |A| > 0 And A[0] = 5
func Cleared(A []int) (first int) {
	lib.Clear(A)
	return A[0]
}

//@ Ensures first = 0

// StillFive wrongly expects the slice to be unchanged.
//
// @ Requires |A| > 0 And A[0] = 5
func StillFive(A []int) (first int) {
	lib.Clear(A)
	return A[0] // want `postcondition may not hold: first = 5`
}

//@ Ensures first = 5

// First inherits when lib.Head succeeds.
func First(A []int) (first int, err error) {
	return lib.Head(A)
}

//@ Ensures |A| > 0 -> err = nil
//@ Ensures err = nil -> first = A[0]

// UsesBroken calls a function whose verification failed in its package.
func UsesBroken(x int) (y int) {
	return lib.Broken(x) // want `the contract of lib.Broken cannot be used: its verification failed in package lib` `cannot verify UsesBroken: Broken has a contract that could not be understood`
}

//@ Ensures y > x

// UsesUnannotated calls an exported function that has no contract.
func UsesUnannotated(x int) (y int) {
	return lib.Unannotated(x) // want `cannot verify UsesUnannotated: it calls Unannotated, which has no contract`
}

//@ Ensures y = x

// UsesWrap calls a function whose proof rests on a failed one.
func UsesWrap(x int) (y int) {
	return lib.Wrap(x) // want `the contract of lib.Wrap cannot be used: its verification failed in package lib` `cannot verify UsesWrap: Wrap has a contract that could not be understood`
}

//@ Ensures y > x

// limit here is not the limit lib's contract speaks of.
const limit = 0

// DividesByLocalLimit satisfies this package's limit, not lib's.
//
// @ Requires n >= 0
func DividesByLocalLimit(n int) (q int) {
	return lib.SafeDivide(n, limit) // want `precondition of SafeDivide may not hold: d >= limit`
}

// DividesByOne satisfies lib's.
//
// @ Requires n >= 0
func DividesByOne(n int) (q int) {
	return lib.SafeDivide(n, 1)
}

//@ Ensures q <= n
