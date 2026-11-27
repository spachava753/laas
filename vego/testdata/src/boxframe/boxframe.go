// Package boxframe lists only a pointer to an element in Modifies, which
// covers that one element (F13 of the review of step 1 of F42).
package boxframe

// Hits counts.
type Hits int

// Reset sets h to zero.
//
// @Requires h != nil
// @Modifies h
// @Ensures *h' = 0
func (h *Hits) Reset() {
	*h = 0
}

// Resetter resets what it holds.
type Resetter interface {
	// @Receiver r
	// @Modifies r
	// @Ensures True
	Reset()
}

// Next lists only p, and resets the element after it through an interface
// value when p is &xs[0]: the footprint is xs[1], which p does not cover.
//
// @Requires p != nil And |xs| > 1
// @Modifies p
// @Ensures True
func Next(p *Hits, xs []Hits) {
	if p == &xs[0] {
		var r Resetter = &xs[1]
		r.Reset() // want `vego: r\.Reset may modify the footprint of r, which Next may not modify; it is the memo`
	}
}

// Keeps relies on Next's frame: false, Next zeroes xs[1].
//
// @Requires |xs| > 1 And xs[1] = 7
// @Modifies xs
// @Ensures xs'[1] = 7
func Keeps(xs []Hits) {
	Next(&xs[0], xs)
}
