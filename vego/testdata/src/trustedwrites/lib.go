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
