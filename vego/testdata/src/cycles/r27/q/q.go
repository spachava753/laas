// Package q calls a function value it finds by assertion.
package q

import "cycles/r27/t"

// Run calls x when it holds a t.Hook.
func Run(x any) int {
	if f, ok := x.(t.Hook); ok {
		return f()
	}
	return 0
}
