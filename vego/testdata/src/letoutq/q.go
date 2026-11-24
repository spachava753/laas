// Package letoutq runs a hook it keeps in its own memory, which another
// package may have stored there (F13 of the design review of package-level
// variables, F30 of the review of step 1 of part 2).
package letoutq

// Hook is what a box holds.
//
// @Ensures True
type Hook func()

// Box holds a hook.
type Box struct{ H Hook }

var box = &Box{}

func current() (b *Box) { return box }

// Slot returns the box, under an entry of the trust file of the tests.
func Slot() (b *Box) { return box }

// Tick runs the hook in the box.
//
// @Ensures True
func Tick(n int) {
	b := current()
	if b != nil && b.H != nil {
		b.H()
	}
}
