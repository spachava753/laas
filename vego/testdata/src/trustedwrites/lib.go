// Package trustedwrites has functions that the trust file of the tests
// gives entries, whose bodies assign a variable.
package trustedwrites

// Ticks counts ticks.
var Ticks int

func bump() { Ticks++ }

// Tick has an entry that lists nothing, though bump assigns Ticks.
func Tick() { bump() }

// TickListed has an entry that lists Ticks.
func TickListed() { Ticks++ }

// TickState has an entry that lists the state of its package.
func TickState() { Ticks++ }

// Table is written through its path by Poke.
var Table = []int{1}

// Poke has an entry that lists nothing, though it writes Table[0].
func Poke() { Table[0] = 5 }

var handedOnly int

// SetHanded sets handedOnly, and is not verified; a value of type
// func(int) may be it.
func SetHanded(k int) { handedOnly = k }

// Apply runs f once, under an entry that lists f under runs and writes
// nothing itself. What f writes is counted at each call, so the entry is
// not reported for it (F27 of the review of the end of part 1).
func Apply(f func(k int)) { f(1) }

var tickHook = func() { Ticks++ }

// TickHook runs a hook of its package, under an entry that lists nothing;
// the hook is no code a caller hands it, so the entry is reported.
func TickHook() { tickHook() }
