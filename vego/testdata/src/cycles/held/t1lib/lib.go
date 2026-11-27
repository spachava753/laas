// Package t1lib is trusted: Run calls N of what it is handed.
package t1lib

import "cycles/held/t1i"

// Run calls x.N().
func Run(x t1i.I) int { return x.N() }
