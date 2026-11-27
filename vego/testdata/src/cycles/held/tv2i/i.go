// Package tv2i declares the types.
package tv2i

// J has M.
type J interface {
	// @Ensures True
	M() (n int)
}

// Hook runs.
//
// @Ensures True
type Hook func() (n int)
