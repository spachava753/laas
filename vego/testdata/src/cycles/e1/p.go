// e1: a method value of a method promoted from an embedded field.
package e1

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.M,\ T\.M\ calls\ run\ at\ p\.go:\d+:\d+,\ run\ calls\ F\ at\ p\.go:\d+:\d+`
}

type T struct{}

func (T) M() int { return run() }

type W struct{ T }

func run() int {
	var w W
	return F(w.M)
}
