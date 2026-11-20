// r5: a bound method value used as a value in the package calls F.
package r5

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.M,\ T\.M\ calls\ F\ at\ p\.go:\d+:\d+`
}

type T struct{}

func (t T) M() int { return F(t.M) }
