// Package ptrifaces holds pointers to interface values: formulas that read
// what they point to (F17 of the review of step 2 of F42), and calls
// through the value under Modifies *p, which names its footprint and its
// states (F18).
package ptrifaces

import "io"

// @Requires p != nil And *p != nil
// @Ensures True
func Check(p *io.Closer) {
}

// Counter counts.
type Counter struct{ N int }

// @Requires c != nil
// @Modifies c
// @Ensures c.N' = 1
func (c *Counter) Bump() {
	c.N = 1
}

// Bumper bumps.
type Bumper interface {
	// @Receiver b
	// @Modifies b
	// @Ensures True
	Bump()
}

// @Requires pb != nil And *pb != nil
// @Modifies *pb
// @Ensures True
func bumpVia(pb *Bumper) {
	(*pb).Bump()
}

// @Requires c != nil And c.N = 0
// @Modifies c
// @Ensures c.N' = 0
func KeepsCounter(c *Counter) {
	var b Bumper = c
	bumpVia(&b)
} // want `vego: postcondition may not hold: c\.N' = 0`

// @Requires c != nil And d != nil And d.N = 0
// @Modifies c
// @Ensures d.N' = 0
func KeepsOther(c, d *Counter) {
	var b Bumper = c
	bumpVia(&b)
} // want `vego: postcondition may not hold: d\.N' = 0`

// Write writes through the value pw points to. That the slot still holds
// a value afterwards is not proved: the footprint of the value is not known
// to be apart from the box that holds it.
//
// @Requires pw != nil And *pw != nil
// @Modifies *pw
// @Ensures True
func Write(pw *io.Writer) {
	_, _ = (*pw).Write([]byte("x"))
}

// @Requires c != nil And d != nil And c != d And d.N = 0
// @Modifies c
// @Ensures d.N' = 0 And c.N' = 1
func KeepsOtherApart(c, d *Counter) {
	var b Bumper = c
	bumpVia(&b)
	c.N = 1
}
