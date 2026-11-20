package r1

type Store interface {
	// @Ensures True
	Read() (n int)
}

// @Requires s != nil
// @Ensures True
func F(s Store) (n int) {
	return s.Read() // want `this\ call\ may\ not\ end:\ F\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ F\ at\ p\.go:\d+:\d+`
}

type T struct{}

func (T) Read() int { return F(T{}) }

func Wire() int { return F(T{}) }
