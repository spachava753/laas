// r13b: an exported method of an unexported type, taken as a method value by
// another package through a value an exported function returns.
package p

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ \(\*t\)\.Hello,\ \(\*t\)\.Hello\ calls\ F\ at\ p\.go:\d+:\d+`
}

type t struct{ f Fn }

// Hello calls F with what t holds.
func (x *t) Hello() int { return F(x.f) }

// New returns a value of the unexported type.
func New() *t { return &t{} }

// Set stores a value in it.
func (x *t) Set(f Fn) { x.f = f }
