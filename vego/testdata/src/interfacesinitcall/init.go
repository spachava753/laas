// Package interfacesinitcall calls through an interface value while its
// variables are initialised.
package interfacesinitcall

import "errors"

// Sizer reports a size.
type Sizer interface {
	// @Ensures 0 <= n <= 100
	Size() (n int)
}

type Small struct{}

// @Ensures 0 <= n <= 100
func (Small) Size() (n int) { return 1 }

var sizer Sizer = Small{}

var size = sizer.Size()

var ErrX = errors.New("x")

// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil { // want `vego: cannot verify Known: ErrX is not known to have its value yet when this runs: `
		return 1
	}
	return 0
}
