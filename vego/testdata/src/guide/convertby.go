package guide

// The programs of the section on converting between interfaces whose
// methods come from other declarations.

// Exact returns what it is given, for numbers that are not negative.
type Exact interface {
	// @Requires n >= 0
	// @Ensures r = n
	Get(n int) (r int)
}

// Natural returns a number that is not negative.
type Natural interface {
	// @Requires n >= 0
	// @Ensures r >= 0
	Get(n int) (r int)
}

// Doubler says less of what it returns.
type Doubler interface {
	// @Requires n >= 0
	// @Ensures r >= n
	Get(n int) (r int)
}

// @Requires x != nil
// @Ensures y != nil
func AsNatural(x Exact) (y Natural) {
	return x
}

// @Requires x != nil
// @Ensures y != nil
func AsExact(x Doubler) (y Exact) {
	return x // want `postcondition may not hold: r = n, in Doubler.Get used as Exact.Get at convertby.go:\d+:\d+`
}
