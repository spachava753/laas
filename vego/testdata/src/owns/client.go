package owns

import "ownslib"

// AddTwo adds twice to a bag of another package, whose declaration travels
// as a fact: Modifies b covers what b owns, and after the first Add what b
// owns is still placed.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func AddTwo(b *ownslib.Bag) {
	b.Add("a")
	b.Add("b")
}

// AddToNew adds to a bag it made, with no Modifies.
//
// @Ensures True
func AddToNew() {
	b := &ownslib.Bag{}
	b.Add("a")
	b.Add("b")
}
