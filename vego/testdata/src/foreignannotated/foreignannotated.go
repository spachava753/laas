// Package foreignannotated stands for a package of another module that
// writes the contract of its interface in source.
package foreignannotated

// Getter gets a number.
type Getter interface {
	// @Ensures n >= 0
	Get() (n int)
}
