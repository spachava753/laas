// Package embeda holds a struct that embeds a number type with pointer
// methods: a call of a promoted method takes the address of the embedded
// field, from any package, so the field lies in the place region of int
// (F1 of the design review of F42).
package embeda

// counter counts.
type counter int

// Ptr returns the counter as an *int.
//
// @Requires c != nil
// @Ensures result != nil
func (c *counter) Ptr() (result *int) {
	return (*int)(c)
}

// inc adds one.
//
// @Requires c != nil And *c < 100
// @Modifies c
// @Ensures *c' = *c + 1
func (c *counter) inc() {
	*c++
}

// S embeds a counter.
type S struct {
	counter
	n int
}

// Bump calls the promoted method on the embedded field.
//
// @Requires s != nil And s.counter < 100
// @Modifies s
// @Ensures True
func (s *S) Bump() {
	s.inc()
}

// Keep writes what p points to and claims s's counter unchanged.
//
// @Requires p != nil And s != nil
// @Modifies p
// @Ensures s.counter' = s.counter
func Keep(p *int, s *S) {
	*p = 7
} // want `vego: postcondition may not hold: s\.counter' = s\.counter`

// Field takes the address of a field named n, of S, by syntax.
//
// @Requires s != nil
// @Ensures True
func Field(s *S) {
	_ = &s.n
}

// plain counts and has value methods only, so a promoted call cannot take
// the address of an embedded plain.
type plain int

// Get returns the count.
//
// @Ensures r = int(c)
func (c plain) Get() (r int) {
	return int(c)
}

// T embeds a plain, whose field keeps the region of its struct.
type T struct {
	plain
	n int
}

// KeepPlain writes what p points to and claims t's plain unchanged, which
// holds: no pointer can point to an embedded plain.
//
// @Requires p != nil And t != nil
// @Modifies p
// @Ensures t.plain' = t.plain
func KeepPlain(p *int, t *T) {
	*p = 7
}
