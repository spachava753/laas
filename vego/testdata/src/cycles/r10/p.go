// r10: a trusted function of the package with runs calls back.
package r10

// @Ensures True
type Fn func() (n int)

func T(f Fn) int { return f() }

// @Ensures True
func F() (n int) {
	return T(h) // want `cannot\ verify\ F:\ h\ may\ call\ through\ a\ function\ value\ or\ an\ interface\ value,\ and\ code\ that\ a\ function\ value\ runs\ cannot\ d`
}

// @Ensures True
func h() (m int) { return F() } // want `this\ call\ may\ not\ end:\ h\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ calls\ T\ at\ p\.go:\d+:\d+,\ T\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h` `recursive\ call\ needs\ a .* annotation\ in\ the\ doc\ comment\ of\ h\ to\ prove\ termination;\ the\ cycle:\ h\ calls\ F\ at\ p\.go`
