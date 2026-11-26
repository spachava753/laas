// Package memnone declares no memory and calls a package verified under a
// declared one: the bound on every value that memdecllib's proofs assume
// is not what memnone's reservations were checked against.
package memnone // want `the verified packages of this build declare different memories under sizes: package memdecllib \(.*memdecllib/vego-trusted.yaml\) declares 256GB, and package memnone \(no trust file\) declares no memory`

import "memdecllib"

// @Ensures r = 1
func One() (r int) {
	return memdecllib.Same(1)
}
