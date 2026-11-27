// Package tvi declares the types.
package tvi

// J has M.
type J interface {
	// @Ensures True
	M() (n int)
}

// Hook runs.
//
// @Ensures True
type Hook func() (n int)
