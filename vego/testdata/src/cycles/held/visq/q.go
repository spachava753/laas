// Package visq calls M of what it is handed, through an interface of its
// own. It does not import visr, so it cannot see that a visr.T may be what
// it is handed.
package visq

// I is called.
type I interface {
	// @Ensures True
	M()
}

// @Requires x != nil
// @Ensures True
func F(x I) { x.M() }
