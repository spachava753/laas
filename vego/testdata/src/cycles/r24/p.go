// r24: a function used as a value of another named type with the same signature.
package r24

// @Ensures True
type Fn func() (n int)

type Gn func() int

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ F\ at\ p\.go:\d+:\d+`
}

func h() int {
	g := Gn(h)
	return F(Fn(g))
}
