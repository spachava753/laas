// e5: precision. A function of a slice parameter is no value of a variadic type.
package e5

// @Ensures True
type Fv func(xs ...int) (n int)

// @Requires f != nil
// @Ensures True
func F(f Fv) (n int) {
	return f(1)
}

type Gs func(xs []int) int

func h(xs []int) int {
	var g Gs = h
	_ = g
	return F(nil)
}
