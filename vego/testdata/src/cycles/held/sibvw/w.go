// Package sibvw wires s and p in verified code.
package sibvw

import (
	"cycles/held/sibvp"
	"cycles/held/sibvs"
)

// Wire registers sibvp.H in s.
//
// @Modifies sibvs
// @Ensures True
func Wire() {
	sibvs.Register(sibvp.H) // want `cannot verify Wire: H may call through a function value or an interface value`
}
