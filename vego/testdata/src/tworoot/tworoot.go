// Package tworoot is built with both modules and has no proofs of its own.
package tworoot // want `the trust files of this build give \(twoentrieslib.Sink\).Put two contracts, at .*twoa/vego-trusted.yaml:4 and at .*twob/vego-trusted.yaml:4; a value that verified code checked against one can reach verified code that relies on the other`

import (
	"twoa"
	"twob"
)

// Use hands the sink of twoa to twob.
func Use() int {
	return twob.F(twoa.Make())
}
