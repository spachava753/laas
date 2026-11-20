// r9b: a method of a generic type implements the interface only once instantiated.
package r9b

type Getter interface {
	// @Ensures True
	Get() (n int)
}

// @Requires g != nil
// @Ensures True
func F(g Getter) (n int) {
	return g.Get() // want `this\ call\ may\ not\ end:\ F\ calls\ g\.Get\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ Box\[X\]\.Get,\ Box\[X\]\.Get\ calls\ F\ at\ p\.go:\d+:\d+`
}

type Box[X any] struct{ x X }

func (b Box[X]) Get() X {
	F(Box[int]{})
	return b.x
}
