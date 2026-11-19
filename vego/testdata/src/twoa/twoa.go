// Package twoa makes a sink checked against the entry of its module.
package twoa

import "twoentrieslib"

// D returns a negative number, which the entry of this module allows.
type D struct{}

// @Ensures y = -1
func (D) Put(x int) (y int) {
	return -1
}

// @Ensures s != nil
func Make() (s twoentrieslib.Sink) {
	return D{}
}
