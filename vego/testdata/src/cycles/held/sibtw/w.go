// Package sibtw wires sibtlib and sibtp in verified code, which is refused:
// sibtlib.Set, which keeps the hook, has no contract.
package sibtw

import (
	"cycles/held/sibtlib"
	"cycles/held/sibtp"
)

// @Ensures True
func Wire() {
	sibtlib.Set(sibtp.H) // want `cannot verify Wire: it calls Set, which has no contract`
}
