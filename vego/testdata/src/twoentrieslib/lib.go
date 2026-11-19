// Package twoentrieslib declares an interface that two modules give
// different entries.
package twoentrieslib

// Sink takes a number.
type Sink interface {
	Put(x int) (y int)
}
