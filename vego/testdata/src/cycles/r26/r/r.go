// Package r runs a method it finds by assertion.
package r

// Run calls Hello on x when x has one.
func Run(x any) int {
	if h, ok := x.(interface{ Hello() int }); ok {
		return h.Hello()
	}
	return 0
}
