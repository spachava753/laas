// Package sibw wires sibr and sibp in verified code, which stratification
// refuses: PT.N calls X, which calls through a value.
package sibw

import (
	"cycles/held/sibp"
	"cycles/held/sibr"
)

// Wire wraps a PT in an sibr.T and hands it to sibp.X.
//
// @Ensures True
func Wire() (n int) {
	return sibp.X(sibr.Wrap(&sibp.PT{})) // want `cannot verify Wire: N may call through a function value or an interface value`
}
