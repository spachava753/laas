// Package sibhi declares the interfaces.
package sibhi

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
