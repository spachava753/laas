// Package tablesclient changes an exported table of package tables.
package tablesclient

import "tables"

// Change writes the table.
func Change() {
	tables.Table[0] = 7 // want `vego: tables.Table may be changed here, but proofs in package tables rely on it holding the value it was declared with`
}
