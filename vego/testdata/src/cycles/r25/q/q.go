// Package q is another package that calls a method it finds by assertion.
package q

// Run calls Hello on x when x has one.
func Run(x any) int {
	if h, ok := x.(interface{ Hello() int }); ok {
		return h.Hello()
	}
	return 0
}
