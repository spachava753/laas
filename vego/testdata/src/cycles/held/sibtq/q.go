// Package sibtq runs the hook lib returns; it does not import p.
package sibtq

import "cycles/held/sibtlib"

// Fire runs lib's current hook.
//
// @Ensures True
func Fire(k int) (n int) {
	h := sibtlib.Current()
	if h == nil {
		return 0
	}
	return h()
}
