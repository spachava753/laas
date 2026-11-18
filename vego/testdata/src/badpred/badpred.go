// Package badpred defines a predicate that cannot be accepted, and a
// function whose contract uses it.
package badpred

// @Predicate Valid(n) ::= DoesNotExist(n) // want `unknown predicate DoesNotExist`

// Value has a contract that means nothing, since Valid does.
//
// @Ensures Valid(result)
func Value() (result int) { return -1 }
