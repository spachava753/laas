// Package sibti declares the hook types.
package sibti

// Hook runs.
//
// @Ensures True
type Hook func() (n int)

// Fn takes a number.
//
// @Ensures True
type Fn func(k int) (n int)
