// r13c: an exported method declared on an unexported type and promoted to an
// exported struct, taken as a method value by another package.
package p

// @Ensures True
type Fn func() (n int)

// @Requires f != nil
// @Ensures True
func F(f Fn) (n int) {
	return f() // want `this\ call\ may\ not\ end:\ F\ calls\ f\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ \(\*inner\)\.Hello,\ \(\*inner\)\.Hello\ calls\ F\ at\ p\.go:\d+:\d+`
}

type inner struct{ f Fn }

func (x *inner) Hello() int { return F(x.f) }

// S is exported and embeds the unexported inner.
type S struct{ *inner }

// NewS returns an S.
func NewS() S { return S{&inner{}} }

// Set stores a value.
func (s S) Set(f Fn) { s.inner.f = f }
