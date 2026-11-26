// Package memdecl declares a memory and calls a package verified with
// none, whose reservations were checked against MaxAlloc only.
package memdecl // want `the verified packages of this build declare different memories under sizes: package memdecl \(.*memdecl/vego-trusted.yaml\) declares 256GB, and package memnonelib \(no trust file\) declares no memory`

import "memnonelib"

// @Ensures r = 1
func One() (r int) {
	return memnonelib.Same(1)
}
