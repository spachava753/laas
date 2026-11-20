// Package globalsleak lets a reference to what globalslib.Plans refers to
// out, by handing it to a function.
package globalsleak

import "globalslib"

func keep(m map[string]int) {}

// Leak is not verified.
func Leak() { keep(globalslib.Plans) } // want `vego: globalslib.Plans may be changed here, but proofs in package globalslib rely on what it refers to being only read`
