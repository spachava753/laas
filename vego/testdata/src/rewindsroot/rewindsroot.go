// Package rewindsroot is built with two modules whose entries of Rewinder's
// method differ only in rewinds, and has no proofs of its own.
package rewindsroot // want `the trust files of this build give \(rewindlib.Rewinder\).Rewind two contracts, at .*rewindsnone/vego-trusted.yaml:6 and at .*rewindsplain/vego-trusted.yaml:\d+`

import (
	"rewindlib"
	"rewindsnone"
	"rewindsplain"
)

// Use hands one Rewinder to both.
func Use(s rewindlib.Rewinder) {
	rewindsnone.Back(s)
	rewindsplain.Back(s)
}
