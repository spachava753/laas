// Package q calls a function value held in a struct it finds by assertion.
package q

// Box holds a function.
type Box struct{ F func() int }

// Run calls what x holds when x is a Box.
func Run(x any) int {
	if b, ok := x.(Box); ok && b.F != nil {
		return b.F()
	}
	return 0
}
