// Package ownslib declares an owner that another package uses.
package ownslib

// Bag owns its slice, which holds at most a thousand items.
//
// @Owns items
// @Invariant |items| <= 1000
type Bag struct {
	items []string
}

// Add appends x unless the bag is full.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func (b *Bag) Add(x string) (added bool) {
	if len(b.items) >= 1000 {
		return false
	}
	b.items = append(b.items, x)
	return true
}
