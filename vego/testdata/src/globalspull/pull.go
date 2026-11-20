// Package globalspull gives the storage of a variable of globalslib to a
// variable of its own, and does not import globalslib.
package globalspull

import _ "unsafe"

//go:linkname limit globalslib.Limit
var limit int

// Set changes globalslib.Limit.
func Set() { limit = 0 }
