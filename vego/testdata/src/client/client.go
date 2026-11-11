// Package client calls verified functions of package lib and relies on the
// contracts that package published.
package client

import "fmt"
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
// @ Modifies A
func Cleared(A []int) (first int) {
	lib.Clear(A)
	return A[0]
}

//@ Ensures first = 0

// StillFive wrongly expects the slice to be unchanged.
//
// @ Requires |A| > 0 And A[0] = 5
// @ Modifies A
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

// Saves uses a struct of another package through its verified methods.
func Saves() int {
	a := lib.Open(50)
	a.Deposit(20)
	a.Deposit(5)
	return a.Balance + a.Limit
}

//@ Ensures result = 75

// SavesTooMuch claims the wrong balance.
func SavesTooMuch() int {
	a := lib.Open(50)
	a.Deposit(20)
	return a.Balance // want `postcondition may not hold: result = 21`
}

//@ Ensures result = 21

// DepositsElsewhere must say that it modifies the account.
//
// @ Requires a != nil And a.Balance = 0
func DepositsElsewhere(a *lib.Account) {
	a.Deposit(1) // want `Deposit may modify what it calls a\.Balance, which DepositsElsewhere may not modify; list it in a //@ Modifies clause`
}

// UsesReset relies on a method whose own verification failed.
//
// @ Requires a != nil
// @ Modifies a.Balance
func UsesReset(a *lib.Account) {
	a.Reset() // want `the contract of \(\*lib.Account\).Reset cannot be used: its verification failed in package lib` `cannot verify UsesReset: Reset has a contract that could not be understood`
}

// TouchesFirst calls a function whose Modifies clause uses a constant of its
// own package, which must keep its value here.
//
// @ Requires |as| = 128 And as[0] != nil And as[127] != nil
// @ Requires as[0] != as[127] And as[0].Balance = 0
// @ Modifies as[127].Balance
func TouchesFirst(as []*lib.Account) int {
	lib.Touch(as) // want `Touch may modify what it calls as\[MaxInt8\].Balance, which TouchesFirst may not modify`
	return as[0].Balance
}

//@ Ensures result = 0

// WrapsLib formats the error of a verified function of another package.
func WrapsLib(x int) (err error) {
	if err := lib.Check(x); err != nil {
		return fmt.Errorf("lib: %w", err)
	}
	return nil
}

//@ Ensures err = nil <-> x >= 0

// WrapsRelay formats an error that another package only passed on.
func WrapsRelay(e error) (err error) {
	if err := lib.Relay(e); err != nil {
		return fmt.Errorf("lib: %w", err) // want `cannot verify WrapsRelay: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

//@ Ensures True

// Forgets assigns to a variable that proofs in lib take to be an error.
func Forgets() {
	lib.ErrGone = nil // want `vego: lib\.ErrGone may be changed here, but proofs in package lib rely on it being the error it was declared with`
}
