// r16: a deferred call through a value.
package r16

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	defer f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ F\ at\ p\.go:\d+:\d+`
	return 0
}

func h() int { return F(h) }
