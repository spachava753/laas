// Package sibhq calls M of what it is handed.
package sibhq

import "cycles/held/sibhi"

// F calls x.M().
//
// @Ensures True
func F(x sibhi.J) (n int) {
	if x == nil {
		return 0
	}
	return x.M()
}
