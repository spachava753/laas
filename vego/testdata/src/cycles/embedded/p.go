// Package embedded: a method promoted from an embedded interface field is a
// call through the interface value, so a cycle through it is found as for
// any interface method (F43, the table of how code is run).
package embedded

// R reads.
type R interface {
	// @Ensures True
	Read() (n int)
}

// S embeds an R.
type S struct{ R }

// T calls F back.
type T struct{ s *S }

// @Requires t != nil
// @Variant 1
// @Ensures True
func (t *T) Read() (n int) {
	if t.s == nil {
		return 0
	}
	return F(*t.s) // want `precondition of F may not hold: s.R != nil` `this call may not end: \(\*T\).Read calls F at p.go:\d+:\d+, F calls s.Read\(\) at p.go:\d+:\d+, which may run \(\*T\).Read`
}

// F calls Read promoted from the embedded R.
//
// @Requires s.R != nil
// @Variant 0
// @Ensures True
func F(s S) (n int) {
	return s.Read() // want `cannot verify F: Read is a method of an interface value that s holds in an embedded field`
}

// Loop is not verified.
func Loop() int {
	t := &T{}
	s := &S{R: t}
	t.s = s
	return F(*s)
}
