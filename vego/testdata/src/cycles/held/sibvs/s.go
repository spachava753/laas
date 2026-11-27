// Package sibvs keeps a hook; it does not import p.
package sibvs

import "cycles/held/sibvi"

var cur sibvi.Hook

// Register keeps h.
//
// @Modifies cur
// @Ensures True
func Register(h sibvi.Hook) { cur = h }

// Fire runs what was registered.
//
// @Ensures True
func Fire(k int) (n int) {
	if cur != nil {
		return cur()
	}
	return 0
}
