// Package globalsroot is built with globalslib and globalsmid, and is
// where the change and the proof that relies on the variable meet.
package globalsroot // want `vego: globalslib.Version is changed at mid.go:8 in package globalsmid, which this package is built with, but proofs in package globalslib rely on it holding the value it was declared with` `vego: globalslib.Limit is changed at pull.go:7 in package globalspull, which this package is built with, but proofs in package globalslib rely on it holding the value it was declared with`

import (
	"globalslib"
	_ "globalsmid"
	_ "globalspull"
)

// Version reads the variable that globalsmid changes.
//
// @Ensures True
func Version() (r int) {
	return len(globalslib.Version) // want `vego: cannot verify Version: globalslib.Version is changed at mid.go:8 in package globalsmid, which this package is built with; package-level variables that are changed are not supported yet`
}
