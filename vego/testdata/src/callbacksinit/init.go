// Package callbacksinit hands, while its variables are initialised, a
// function literal to a trusted function of its own that calls it, so it
// relies on none of its error variables.
package callbacksinit

import "errors"

func each(n int, f func(i int)) {
	for i := 0; i < n; i++ {
		f(i)
	}
}

var ran = func() int {
	each(2, func(i int) {})
	return 0
}()

var ErrX = errors.New("x")

// Known is 1 because ErrX is not nil, which is known only in a package
// where no code of the package can run before ErrX has its value.
//
// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil { // want `vego: cannot verify Known: ErrX is not known to have its value yet when this runs`
		return 1
	}
	return 0
}
