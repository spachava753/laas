// e6: a function used as a value of an alias of its signature.
package e6

// @Ensures True
type Fn func() (n int)

type A = func() int

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ F\ at\ p\.go:\d+:\d+`
}

func h() int {
	var a A = h
	return F(a)
}
