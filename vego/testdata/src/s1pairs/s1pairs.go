// Package s1pairs holds the pairs S1 must not separate (F6 of the design
// review of F42): two struct types that differ only in their tags, which
// convert to each other and share their memory, and a field of a named
// number type that a pointer to its underlying type points to.
package s1pairs

// Tagged has tags.
type Tagged struct {
	X int `json:"x"`
	Y int `json:"y"`
}

// Plain has the same fields without tags.
type Plain struct {
	X int
	Y int
}

// ThroughPlain writes a Tagged through a pointer converted to a Plain.
//
// @Requires t != nil
// @Modifies t
// @Ensures t.X' = 1 And t.Y' = t.Y
func ThroughPlain(t *Tagged) {
	p := (*Plain)(t)
	p.X = 1
}

// ThroughPlainWrong claims the write is not seen.
//
// @Requires t != nil And t.X < 100
// @Modifies t
// @Ensures t.X' = t.X
func ThroughPlainWrong(t *Tagged) {
	p := (*Plain)(t)
	p.X = t.X + 1
} // want `vego: postcondition may not hold: t\.X' = t\.X`

// ThroughTagged writes a Plain through a pointer converted to a Tagged.
//
// @Requires p != nil
// @Modifies p
// @Ensures p.Y' = 2 And p.X' = p.X
func ThroughTagged(p *Plain) {
	t := (*Tagged)(p)
	t.Y = 2
}

// ThroughTaggedWrong claims the write is not seen.
//
// @Requires p != nil And p.Y < 100
// @Modifies p
// @Ensures p.Y' = p.Y
func ThroughTaggedWrong(p *Plain) {
	t := (*Tagged)(p)
	t.Y = p.Y + 1
} // want `vego: postcondition may not hold: p\.Y' = p\.Y`

// Count is a named number.
type Count int

// Meter holds a Count whose address is taken, so it lies in the place
// region of int.
type Meter struct {
	c Count
	n int
}

// SetVia writes the Count through a pointer to an int.
//
// @Requires m != nil
// @Modifies m
// @Ensures m.c' = 3 And m.n' = m.n
func SetVia(m *Meter) {
	p := (*int)(&m.c)
	*p = 3
}

// Keep writes what p points to and claims the Count unchanged, which
// does not hold when p points to it.
//
// @Requires p != nil And m != nil
// @Modifies p
// @Ensures m.c' = m.c
func Keep(p *int, m *Meter) {
	*p = 7
} // want `vego: postcondition may not hold: m\.c' = m\.c`
