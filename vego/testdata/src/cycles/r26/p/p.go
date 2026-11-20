// r26: an interface value handed to another package, whose dynamic type is a
// type of a third package that embeds a type of this package; the embedded
// type does not implement the interface, but its exported method is promoted.
package p

import "cycles/r26/r"

// I is what F is handed.
type I interface {
	// @Ensures True
	Foo() (n int)
}

// @Requires x != nil
// @Ensures True
func F(x I) (n int) {
	return r.Run(x) // want `this\ call\ may\ not\ end:\ F\ hands\ x\ to\ r\.Run\(x\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Hello,\ T\.Hello\ calls\ F\ at\ p\.go:\d+:\d+`
}

// T has no Foo, so it does not implement I.
type T struct{ X I }

// Hello calls F.
func (t T) Hello() int { return F(t.X) }
