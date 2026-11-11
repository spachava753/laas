// Package usesbadpred calls a function of a package whose predicates could
// not be accepted. Its contract must not count as established.
package usesbadpred

import "badpred"

// Use relies on a contract stated with a broken predicate.
func Use() int {
	return badpred.Value() // want `the contract of badpred.Value cannot be used: its verification failed in package badpred` `cannot verify Use: Value has a contract that could not be understood`
}

//@ Ensures True
