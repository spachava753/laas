// Package inputsdecl declares that inputs end and calls a package verified
// without the declaration.
package inputsdecl // want `the verified packages of this build declare different inputs: package inputsdecl \(.*inputsdecl/vego-trusted.yaml\) declares 1TB, and package memnonelib \(no trust file\) declares no inputs`

import "memnonelib"

// @Ensures r = 1
func One() (r int) {
	return memnonelib.Same(1)
}
