// Package tv2q calls M of what it is handed.
package tv2q

import "cycles/held/tv2i"

// F calls x.M().
//
// @Ensures True
func F(x tv2i.J) (n int) {
	if x == nil {
		return 0
	}
	return x.M()
}
