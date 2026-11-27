// Package libg holds a Genner whose Gen hands what it holds to slices.Index
// with a type argument that can hold code, which its entry claims nothing
// of.
package libg

import "slices"

// Genner generates.
type Genner interface {
	// @Ensures True
	Gen()
}

// Generic is not verified.
type Generic struct{ V any }

func (g Generic) Gen() { _ = slices.Index([]any{g.V}, nil) }

// Mark is verified, so that the package publishes what its functions run.
//
// @Ensures True
func Mark() {}
