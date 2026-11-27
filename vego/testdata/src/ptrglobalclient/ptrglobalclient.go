// Package ptrglobalclient takes the address of ptrgloballib.N and hands it
// to F, which relies on no pointer pointing to N.
package ptrglobalclient

import "ptrgloballib"

// Use is false: F writes ptrgloballib.N through p.
//
// @Ensures r = 0
func Use() (r int) {
	if ptrgloballib.N != 0 { // want `vego: cannot verify Use: ptrgloballib\.N is changed in this package; package-level variables that are changed are not supported yet`
		return 0
	}
	ptrgloballib.F(&ptrgloballib.N) // want `vego: ptrgloballib\.N may be changed here, but proofs in package ptrgloballib rely on its address never being taken`
	return ptrgloballib.N
}
