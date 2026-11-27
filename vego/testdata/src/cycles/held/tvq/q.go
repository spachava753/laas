// Package tvq calls M of what it is handed.
package tvq

import "cycles/held/tvi"

// F calls x.M().
//
// @Ensures True
func F(x tvi.J) (n int) {
	if x == nil {
		return 0
	}
	return x.M()
}
