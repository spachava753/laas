// r11: a trusted function of the package with calls is handed a function that calls back.
package r11

func T(f func() int) int { return f() }

// @Ensures True
func F() (n int) {
	return T(h) // want `recursive\ call\ needs\ a .* annotation\ in\ the\ doc\ comment\ of\ F\ to\ prove\ termination;\ the\ cycle:\ F\ calls\ h\ at\ p\.go`
}

// @Ensures True
func h() (m int) { return F() } // want `recursive\ call\ needs\ a .* annotation\ in\ the\ doc\ comment\ of\ h\ to\ prove\ termination;\ the\ cycle:\ h\ calls\ F\ at\ p\.go`
