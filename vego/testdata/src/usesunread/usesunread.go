// Package usesunread calls functions of a package in which an annotation
// was not read. Their contracts must not count as established.
package usesunread

import "unread"

// Use relies on the contract of the function the comment stood in.
//
// @Ensures result = 0
func Use() (result int) {
	return unread.Value() // want `the contract of unread.Value cannot be used: its verification failed in package unread` `cannot verify Use: Value has a contract that could not be understood`
}

// UseOther relies on another function of that package.
//
// @Ensures result = 1
func UseOther() (result int) {
	return unread.Other() // want `the contract of unread.Other cannot be used: its verification failed in package unread` `cannot verify UseOther: Other has a contract that could not be understood`
}
