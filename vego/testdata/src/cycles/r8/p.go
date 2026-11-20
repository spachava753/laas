// r8: a call of a method of an embedded interface.
package r8

type Store interface {
	// @Ensures True
	Read() (n int)
}

type RS interface {
	Store
	// @Ensures True
	Close() (n int)
}

// @Requires s != nil
// @Ensures True
func F(s RS) (n int) {
	return s.Read() // want `this\ call\ may\ not\ end:\ F\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ F\ at\ p\.go:\d+:\d+`
}

type T struct{}

func (T) Read() int  { return F(T{}) }
func (T) Close() int { return 0 }
