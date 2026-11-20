// r32: H is reached from G by a static call and by a call through an interface;
// only the second makes F -> G -> ... -> H -> F a cycle through an unresolved edge.
package r32

type Store interface {
	// @Ensures True
	Read() (n int)
}

// @Requires n >= 0 And s != nil
// @Variant 3 * n + 2
// @Ensures True
func F(n int, s Store) (r int) {
	if n == 0 {
		return 0
	}
	return G(n, s) // want `this\ call\ may\ not\ end:\ F\ calls\ G\ at\ p\.go:\d+:\d+,\ G\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ H\ at\ p\.go:\d+:\d+,\ H\ calls\ F\ at\ p\.go:\d+:\d+`
}

// @Requires n >= 1 And s != nil
// @Variant 3 * n + 1
// @Ensures True
func G(n int, s Store) (r int) {
	s.Read() // want `this\ call\ may\ not\ end:\ G\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ H\ at\ p\.go:\d+:\d+,\ H\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ calls\ G\ at\ p\.go:\d+:\d+`
	return H(n, s)
}

// @Requires n >= 1 And s != nil
// @Variant 3 * n
// @Ensures True
func H(n int, s Store) (r int) {
	return F(n-1, s) // want `this\ call\ may\ not\ end:\ H\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ calls\ G\ at\ p\.go:\d+:\d+,\ G\ calls\ s\.Read\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Read,\ T\.Read\ calls\ H\ at\ p\.go:\d+:\d+`
}

// T's Read calls H.
type T struct{}

func (t T) Read() int { return H(5, t) }
