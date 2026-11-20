// e4: a function passed through a generic function that returns it.
package e4

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h,\ h\ calls\ F\ at\ p\.go:\d+:\d+`
}

func Wrap[T any](f func() T) func() T { return f }

func h() int { return F(Wrap(h)) }
