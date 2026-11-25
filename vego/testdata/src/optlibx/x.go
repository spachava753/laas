// Package optlibx is another module with an interface that one trust file
// of the build gives an entry and the other does not (D5 of F35).
package optlibx

// Sizer reports a size.
type Sizer interface {
	Size() (n int)
}
