// Package globalsmid changes a variable of globalslib, and is not
// verified.
package globalsmid

import "globalslib"

func init() {
	globalslib.Version = "1.0" // want `vego: globalslib.Version may be changed here, but proofs in package globalslib rely on it holding the value it was declared with`
}
