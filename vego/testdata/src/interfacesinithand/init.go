// Package interfacesinithand hands a value converted to an interface to a
// function of another package while its variables are initialised. That
// function may call its methods before ErrX has its value.
package interfacesinithand

import (
	"errors"
	"interfaceslib"
)

type Small struct{}

// @Ensures 0 <= n <= 100
func (Small) Size() (n int) { return 1 }

var measured = interfaceslib.Measure(Small{})

var ErrX = errors.New("x")

// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil { // want `vego: cannot verify Known: ErrX is not known to have its value yet when this runs: `
		return 1
	}
	return 0
}
