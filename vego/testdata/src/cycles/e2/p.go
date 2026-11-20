// e2: a function stored by a package-level initialiser.
package e2

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ F\ at\ p\.go:\d+:\d+`
}

var table = []Fn{h}

var cur Fn

func init() { cur = table[0] }

func h() int { return F(cur) }
