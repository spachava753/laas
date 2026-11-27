// Package sibi declares the interfaces.
package sibi

// I has N.
type I interface {
	// @Ensures True
	N() (n int)
}

// J has M.
type J interface {
	// @Ensures True
	M() (n int)
}
