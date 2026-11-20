// r17: a call through a value inside a literal called in place.
package r17

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	n = func() (m int) { return f() }() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ F\ at\ p\.go:\d+:\d+`
	return n
}

func h() int { return F(h) }
