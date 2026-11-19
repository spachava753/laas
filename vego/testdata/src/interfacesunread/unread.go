// Package interfacesunread has an annotation that is not read, so none of
// its contracts is handed to other packages as verified.
package interfacesunread

// Counter counts.
type Counter interface {
	// @Ensures n >= 0
	Count() (n int)
}

// @Ensure True // want `unknown annotation "Ensure"`
func Stray() {}
