// Package tvv keeps a hook and runs it; it is verified.
package tvv

import "cycles/held/tvi"

var cur tvi.Hook

// Register keeps h.
//
// @Modifies cur
// @Ensures True
func Register(h tvi.Hook) { cur = h }

// Fire runs what was registered.
//
// @Ensures True
func Fire(k int) (n int) {
	if cur != nil {
		return cur()
	}
	return 0
}
