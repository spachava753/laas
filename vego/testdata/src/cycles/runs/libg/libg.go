// Package libg holds a Genner whose Gen hands what it holds to slices.Index
// with a type argument that can hold code. The entry of slices.Index claims
// under asserts that it runs nothing of a value of S or E, so nothing of
// the slice it is handed, which holds only such values: Gen runs nothing
// (F43, step 2; before, s was read strictly and Gen could run anything).
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
