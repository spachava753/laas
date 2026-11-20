// e7: a method value of an interface embedded in a struct.
package e7

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

type W struct{ Store }

type T struct{}

func (T) Read() int {
	w := W{T{}}
	return F(w.Read)
}
