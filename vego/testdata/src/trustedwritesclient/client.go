// Package trustedwritesclient calls the functions of trustedwrites under
// their entries (F10 of the design review of package-level variables).
package trustedwritesclient

import "trustedwrites"

// Same keeps Ticks across a call whose entry lists nothing, which the
// body of the function shows to be false.
//
// @Ensures same
func Same() (same bool) {
	a := trustedwrites.Ticks
	trustedwrites.Tick() // want `^vego: the trusted contract of Tick does not list trustedwrites.Ticks, which its body writes at lib.go:8 in bump; an entry lists what its function changes, as in modifies: \[Ticks\]$`
	return trustedwrites.Ticks == a
}

// Listed forgets Ticks across a call whose entry lists it.
//
// @Modifies trustedwrites.Ticks
// @Ensures same
func Listed() (same bool) {
	a := trustedwrites.Ticks
	trustedwrites.TickListed()
	return trustedwrites.Ticks == a // want `^vego: postcondition may not hold: same$`
}

// State forgets Ticks across a call whose entry lists the state of its
// package.
//
// @Modifies trustedwrites
// @Ensures same
func State() (same bool) {
	a := trustedwrites.Ticks
	trustedwrites.TickState()
	return trustedwrites.Ticks == a // want `^vego: postcondition may not hold: same$`
}

// StateUnlisted does not list what the entry changes.
//
// @Ensures True
func StateUnlisted() {
	trustedwrites.TickState() // want `^vego: TickState may modify what trustedwrites.Table refers to, part of the state of package trustedwrites, which StateUnlisted may not modify; list trustedwrites in a // @Modifies clause$`
}

// Ticked uses the entry of Tick one call down from where Ticks is read
// (F24 of the review of step 4).
//
// @Ensures True
func Ticked() {
	trustedwrites.Tick() // want `^vego: the trusted contract of Tick does not list trustedwrites.Ticks, which its body writes at lib.go:8 in bump; an entry lists what its function changes, as in modifies: \[Ticks\]$`
}

// AroundTicked relies on Ticks across Ticked.
//
// @Ensures same
func AroundTicked() (same bool) {
	a := trustedwrites.Ticks
	Ticked()
	return trustedwrites.Ticks == a
}

// Poked keeps Table's contents across a call whose body writes them.
//
// @Requires |trustedwrites.Table| > 0
// @Ensures same
func Poked() (same bool) {
	a := trustedwrites.Table[0]
	trustedwrites.Poke() // want `^vego: the trusted contract of Poke does not list trustedwrites.Table, which its body writes at lib.go:\d+; an entry lists what its function changes, as in modifies: \[Table\]$`
	return trustedwrites.Table[0] == a
}

// Applies hands Apply a literal that writes nothing; Apply's entry is true.
//
// @Ensures True
func Applies() {
	trustedwrites.Apply(func(k int) {})
}

// Hooked calls TickHook, whose entry does not list what its hook writes.
//
// @Ensures True
func Hooked() {
	trustedwrites.TickHook() // want `^vego: the trusted contract of TickHook does not list trustedwrites.Table, which its body writes at lib.go:\d+ in code that a call through a value may run; an entry lists what its function changes, as in modifies: \[Table\]$` `^vego: the trusted contract of TickHook does not list trustedwrites.Ticks, which its body writes at lib.go:8 in bump in code that a call through a value may run; an entry lists what its function changes, as in modifies: \[Ticks\]$`
}
