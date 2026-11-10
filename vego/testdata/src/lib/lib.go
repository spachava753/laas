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
//
// @ Modifies A
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

// Account is a struct that other packages use through its methods.
type Account struct {
	Balance int
	Limit   int
	history []int
}

// Open returns a new account.
//
// @ Requires limit >= 0
func Open(limit int) *Account {
	return &Account{Limit: limit}
}

//@ Ensures fresh(result) And result.Balance = 0 And result.Limit = limit

// Deposit adds to the balance and to nothing else.
//
// @ Requires a != nil And 0 <= amount <= 1000 And 0 <= a.Balance <= 1000000
// @ Modifies a.Balance
func (a *Account) Deposit(amount int) {
	a.Balance += amount
}

//@ Ensures a.Balance' = a.Balance + amount

// Reset claims to modify only the balance but also clears the limit.
//
// @ Requires a != nil
// @ Modifies a.Balance
func (a *Account) Reset() {
	a.Balance = 0
	a.Limit = 0 // want `a\.Limit is assigned, which Reset may not modify; list it in a //@ Modifies clause`
}

//@ Ensures a.Balance' = 0

// MaxInt8 has the name of a built-in limit and another value.
const MaxInt8 = 0

// Touch names what it modifies with a constant of this package.
//
// @ Requires |as| = 128 And as[0] != nil
// @ Modifies as[MaxInt8].Balance
func Touch(as []*Account) {
	as[MaxInt8].Balance = 1
}

// Check returns an error it made itself, which callers may format.
func Check(x int) (err error) {
	if x < 0 {
		return errEmpty
	}
	return nil
}

//@ Ensures err = nil <-> x >= 0

// Relay returns the error it was given, which nobody may format.
func Relay(e error) (err error) {
	return e
}

//@ Ensures (err = nil) <-> (e = nil)
