// e3: a function in a composite literal of another package's struct.
package p

import "cycles/e3/q"

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ F\ at\ p\.go:\d+:\d+`
}

func h() int {
	s := q.S{H: h}
	return F(Fn(s.H))
}
