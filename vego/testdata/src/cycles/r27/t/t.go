// Package t declares a contracted function type.
package t

// Hook returns a number.
//
// @Ensures True
type Hook func() (n int)
