// Package optroot is built with both modules and has no proofs of its own.
package optroot // want `the trust files of this build give entries to different interfaces that values of optlib.W are checked against where they are converted: package opta counts optlibx.Sizer, from the entries at .*opta/vego-trusted.yaml:4, and package optb does not`

import (
	"opta"
	"optb"
)

// Use hands what optb makes to opta.
func Use() int {
	return opta.SizeOf(optb.Make())
}
