// Package placefields holds the programs that guard how a read of a field
// that lies in the region of its type (F42) sees the writes made before
// it: which writes it may pass over (R6), and which it may not.
package placefields

// A has two exported numbers, which lie in the region of int with every
// other exported int field.
type A struct {
	X, Y int
}

// B holds an A, so a write through a B may write the A inside it.
type B struct {
	In A
	Z  int
}

// C holds no A, and an A holds no C.
type C struct {
	W int
}

// OtherType writes a C between the write and the read of an A: the two
// values do not overlap, so the read passes over it.
//
// @Requires a != nil And c != nil
// @Modifies a.X, c.W
// @Ensures a.X' = 1 And c.W' = 2
func OtherType(a *A, c *C) {
	a.X = 1
	c.W = 2
}

// OtherField writes another field of a value of the same type: the two
// values are one or apart, so the cells differ.
//
// @Requires a != nil And b != nil
// @Modifies a.X, b.Y
// @Ensures a.X' = 1 And b.Y' = 2
func OtherField(a, b *A) {
	a.X = 1
	b.Y = 2
}

// SameField writes the same field of two values of one type, which may be
// one value.
//
// @Requires a != nil And b != nil
// @Modifies a.X, b.X
// @Ensures a.X' = 1
func SameField(a, b *A) {
	a.X = 1
	b.X = 2
} // want `vego: postcondition may not hold: a\.X' = 1`

// Inside writes the A inside a B through the B, and reads it through a
// pointer to it: a B holds an A, so the write is seen.
//
// @Requires b != nil
// @Modifies b
// @Ensures r = 3
func Inside(b *B) (r int) {
	a := &b.In
	b.In.X = 3
	return a.X
}

// InsideWrong claims the read through the inner pointer does not see the
// write through the outer one.
//
// @Requires b != nil And a = &b.In And b.In.X < 100
// @Modifies b
// @Ensures a.X' = a.X
func InsideWrong(b *B, a *A) {
	b.In.X = a.X + 1
} // want `vego: postcondition may not hold: a\.X' = a\.X`

// Stale writes c.X in a loop through a variable the loop assigns, beside a
// write of a C: the loop forgets the region with a layer whose targets are
// the frame, which holds only b. The read of r.X in the Ensures must not
// pass over that layer because its targets are of another type (F8 of the
// design review of F42), since c was made after entry and lies in no
// target. The claim is false for n > 0.
//
// @Requires b != nil And 0 <= n < 100
// @Modifies b
// @Ensures r != nil And r.X = 0
func Stale(b *C, n int) (r *A) {
	c := &A{}
	a := c
	// @Invariant 0 <= i <= n And a = c And c != nil And fresh(c)
	// @Variant n - i
	for i := 0; i < n; i++ {
		a.X = 1
		b.W = 2
		a = c
	}
	return c // want `vego: postcondition may not hold: r\.X = 0`
}
