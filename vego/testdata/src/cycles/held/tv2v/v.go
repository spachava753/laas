// Package tv2v keeps a hook and runs it; it is verified.
package tv2v

import "cycles/held/tv2i"

var cur tv2i.Hook

// Register keeps h.
//
// @Modifies cur
// @Ensures True
func Register(h tv2i.Hook) { cur = h }

// Fire runs what was registered.
//
// @Ensures True
func Fire(k int) (n int) {
	if cur != nil {
		return cur()
	}
	return 0
}
