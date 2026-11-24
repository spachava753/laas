// Package typeonlylib has no function with annotations, only the contract
// of a function type, and a variable of it whose literal does not meet it
// (S3 of F31's coder, built in F32).
package typeonlylib

// Clock returns a positive count.
//
// @Ensures t > 0
type Clock func() (t int)

// Now is a clock that returns -1.
var Now Clock = func() (t int) { return -1 }

// Good is one that meets the contract.
var Good Clock = func() (t int) { return 1 }
