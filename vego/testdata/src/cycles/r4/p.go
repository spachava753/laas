package r4

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ G\ at\ p\.go:\d+:\d+,\ G\ calls\ F\ at\ p\.go:\d+:\d+`
}

// @Requires f != nil
// @Ensures True
func G(f Fn) (n int) {
	return F(f) // want `this\ call\ may\ not\ end:\ G\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ G\ at\ p\.go:\d+:\d+`
}

func h() int { return G(h) }
