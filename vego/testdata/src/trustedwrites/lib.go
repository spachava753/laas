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
