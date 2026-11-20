// r13: an exported function of the package made into a value only by another package.
package p

// @Ensures True
type Fn func(k K) (n int)

// K carries a value.
type K struct{ F Fn }

// @Requires k.F != nil
// @Ensures True
func F(k K) (n int) {
	return k.F(k) // want `this\ call\ may\ not\ end:\ F\ calls\ k\.F\(k\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ F`
}

// H is never used as a value in this package.
func H(k K) int { return F(k) }
