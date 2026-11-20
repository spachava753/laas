package r2

type Store interface {
	// @Ensures True
	Read() (n int)
}

// @Requires s != nil
// @Ensures True
func F(s Store) (n int) {
	return s.Read() // want `this\ call\ may\ not\ end:\ F\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ G\ at\ p\.go:\d+:\d+,\ G\ calls\ F\ at\ p\.go:\d+:\d+`
}

// @Requires s != nil
// @Ensures True
func G(s Store) (n int) {
	return F(s) // want `this\ call\ may\ not\ end:\ G\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ G\ at\ p\.go:\d+:\d+`
}

type T struct{}

func (T) Read() int { return G(T{}) }
