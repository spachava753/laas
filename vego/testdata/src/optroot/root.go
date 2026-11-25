// Package optroot is built with both modules and has no proofs of its own.
package optroot // want `the trust files of this build give entries to different interfaces, against which values are checked where they are converted: the proofs of package opta count optlibx.Sizer, which .*opta/vego-trusted.yaml gives entries, and those of package optb do not`

import (
	"opta"
	"optb"
)

// Use hands what optb makes to opta.
func Use() int {
	return opta.SizeOf(optb.Make())
}
