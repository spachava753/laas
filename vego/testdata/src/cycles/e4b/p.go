// e4b: a literal made inside a generic function, returned as a value.
package e4b

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ the\ function\ literal\ at\ p\.go:\d+:\d+,\ the\ function\ literal\ at\ p\.go:\d+:\d+\ calls\ F\ at\ p\.go:\d+:\d+`
}

func Mk[T any]() func() T {
	return func() T {
		var t T
		F(Mk[int]())
		return t
	}
}
