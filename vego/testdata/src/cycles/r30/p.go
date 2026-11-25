// r30: a literal made in a verified function whose verification stops before it.
package r30

// Fn is a contracted function type.
//
// @Ensures True
type Fn func() (n int)

// Box holds a value.
type Box struct{ f Fn }

// G cannot be verified (copy of strings), and makes a literal after that.
//
// @Requires b != nil And |d| = 1 And |s| = 1
// @Modifies b, d
// @Ensures True
func G(b *Box, d, s []string) {
	copy(d, s) // want `cannot verify G: copy of a slice of string is not supported yet`
	b.f = func() (n int) { return H(b) }
}

// H calls what b holds.
//
// @Requires b != nil And b.f != nil
// @Ensures True
func H(b *Box) (n int) {
	return b.f() // want `this\ call\ may\ not\ end:\ H\ calls\ b\.f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ the\ function\ literal\ at\ p\.go:\d+:\d+,\ the\ function\ literal\ at\ p\.go:\d+:\d+\ calls\ H\ at\ p\.go:\d+:\d+`
}

// wire is not verified.
func wire() {
	b := &Box{}
	G(b, []string{"a"}, []string{"b"})
	H(b)
}
