// r7: an interface method value used as a value of the function type.
package r7

type Store interface {
	// @Ensures True
	Read() (n int)
}

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ F\ at\ p\.go:\d+:\d+`
}

type T struct{}

func (T) Read() int {
	var s Store = T{}
	return F(s.Read)
}
