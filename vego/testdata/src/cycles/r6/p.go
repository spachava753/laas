// r6: a method expression used as a value calls F.
package r6

type T struct{}

// @Ensures True
type Fn func(t T) (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f(T{}) // want `this\ call\ may\ not\ end:\ F\ calls\ f\(T\{\}\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.M,\ T\.M\ calls\ F\ at\ p\.go:\d+:\d+`
}

func (t T) M() int { return F(T.M) }
