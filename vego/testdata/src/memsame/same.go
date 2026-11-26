// Package memsame declares the memory its verified dependency declares.
package memsame

import "memsamelib"

// @Ensures r = 1
func One() (r int) {
	return memsamelib.Same(1)
}
