// Package wrapsroot is built with both, and is where the change and the
// proof that relies on io.EOF through ErrRead meet.
package wrapsroot // want `vego: io.EOF is changed at wrapsmid.go:13 in package wrapsmid, which this package is built with, but proofs in package wrapsp rely on it being the error it was declared with`

import (
	_ "wrapsmid"
	"wrapsp"
)

// Read cannot take ErrRead to hold what it was declared with.
//
// @Ensures err != nil
func Read() (err error) {
	return wrapsp.ErrRead // want `vego: cannot verify Read: io.EOF, which went into wrapsp.ErrRead, is changed at wrapsmid.go:13 in package wrapsmid, which this package is built with, so it is not known to hold the error it was declared with`
}
