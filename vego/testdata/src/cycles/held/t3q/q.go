// Package t3q runs the current hook.
package t3q

import "cycles/held/t3lib"

// Fire runs lib's current hook.
//
// @Ensures True
func Fire(k int) (n int) {
	h := t3lib.Current()
	if h == nil {
		return 0
	}
	return h()
}
