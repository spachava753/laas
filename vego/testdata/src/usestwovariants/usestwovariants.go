// Package usestwovariants calls a function one of whose clauses was dropped.
package usestwovariants

import "twovariants"

// Use relies on its contract.
//
// @Ensures result = 0
func Use() (result int) {
	return twovariants.Down(3) // want `the contract of twovariants.Down cannot be used: its verification failed in package twovariants`
}
