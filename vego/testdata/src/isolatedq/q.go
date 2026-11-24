// Package isolatedq is not verified; its entries claim to be isolated.
package isolatedq

// Box holds a function.
type Box struct{ H func() }

// Hand runs what b holds.
func Hand(b *Box) {
	if b.H != nil {
		b.H()
	}
}

// Plain holds a number.
type Plain struct{ N int }

// Look reads b.
func Look(b *Plain) int { return b.N }
