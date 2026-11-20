// r28: a call that is on a resolved cycle with variants and on a cycle through an interface call.
package r28

type Store interface {
	// @Ensures True
	Read() (n int)
}

// @Requires n >= 0 And s != nil
// @Variant n
// @Ensures True
func F(n int, s Store) (r int) {
	if n == 0 {
		return 0
	}
	return G(n-1, s) // want `this\ call\ may\ not\ end:\ F\ calls\ G\ at\ p\.go:\d+:\d+,\ G\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ F\ at\ p\.go:\d+:\d+`
}

// @Requires n >= 0 And s != nil
// @Variant n
// @Ensures True
func G(n int, s Store) (r int) {
	s.Read() // want `this\ call\ may\ not\ end:\ G\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ calls\ G\ at\ p\.go:\d+:\d+`
	return F(n, s) // want `variant\ may\ not\ decrease\ in\ recursive\ call:\ n`
}

// T's Read calls F.
type T struct{}

func (t T) Read() int { return F(1, t) }
