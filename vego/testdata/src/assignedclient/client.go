// Package assignedclient takes the address of a variable whose address
// assignedlib relies on never being taken (F2 of the design review).
package assignedclient

import "assignedlib"

// Main hands Bump the variable's own address, and Bump returns false.
func Main() bool {
	return assignedlib.Bump(&assignedlib.Cfg) // want `^vego: assignedlib.Cfg may be changed here, but proofs in package assignedlib rely on its address never being taken and no directive naming it$`
}
