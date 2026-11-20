// Package hole is the cycle that verified before what the trial found
// wrong (F17): variants were checked only at calls with a static callee,
// so F and (*T).Read verified with any variants, and Loop runs out of
// stack. A cycle through a call of an interface method is now reported at
// each call of it.
package hole

// Store reads data.
type Store interface {
	// @Ensures True
	Read() (n int)
}

// T calls back.
type T struct{ s Store }

// @Requires t != nil
// @Variant 1
// @Ensures True
func (t *T) Read() (n int) {
	if t.s == nil {
		return 0
	}
	return F(t.s) // want `this call may not end: \(\*T\).Read calls F at hole.go:\d+:\d+, F calls s.Read\(\) at hole.go:\d+:\d+, which may run \(\*T\).Read; a cycle that goes through a call with no static callee`
}

// @Requires s != nil
// @Variant 0
// @Ensures True
func F(s Store) (n int) {
	return s.Read() // want `this call may not end: F calls s.Read\(\) at hole.go:\d+:\d+, which may run \(\*T\).Read, \(\*T\).Read calls F at hole.go:\d+:\d+`
}

// Loop is not verified: it converts T to Store.
func Loop() int {
	p := &T{}
	p.s = p
	return F(p)
}
