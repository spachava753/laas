// r9: a generic function instantiated as a value calls F.
package r9

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ G,\ G\ calls\ F\ at\ p\.go:\d+:\d+`
}

func G[X any]() X {
	var x X
	F(G[int])
	return x
}
