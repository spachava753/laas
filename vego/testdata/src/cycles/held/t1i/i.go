// Package t1i declares the interfaces.
package t1i

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
