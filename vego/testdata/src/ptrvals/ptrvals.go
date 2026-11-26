// Package ptrvals has pointers to numbers, booleans, and strings, as
// ordinary code writes them.
package ptrvals

// Inc increments what p points to.
//
// @Requires p != nil And *p < 1000
// @Modifies p
// @Ensures *p' = *p + 1
func Inc(p *int) {
	*p = *p + 1
}

// IncLocal increments a local variable through its address.
//
// @Ensures r = 6
func IncLocal() (r int) {
	x := 5
	Inc(&x)
	return x
}

// IncNew increments a new int twice.
//
// @Ensures r = 2
func IncNew() (r int) {
	p := new(int)
	Inc(p)
	Inc(p)
	return *p
}

// ReadAfterWrite reads x through p after x is assigned.
//
// @Ensures r = 2
func ReadAfterWrite() (r int) {
	x := 5
	p := &x
	x = 2
	return *p
}

// WriteThrough assigns x through p.
//
// @Ensures r = 3
func WriteThrough() (r int) {
	x := 5
	p := &x
	*p = 3
	return x
}

// Add adds what q points to into what p points to; p and q may be equal.
//
// @Requires p != nil And q != nil
// @Requires 0 <= *p <= 1000 And 0 <= *q <= 1000
// @Modifies p
// @Ensures *p' = *p + *q
func Add(p, q *int) {
	*p = *p + *q
}

// Swap swaps what p and q point to; p and q may be equal.
//
// @Requires p != nil And q != nil
// @Modifies p, q
// @Ensures *p' = *q And *q' = *p
func Swap(p, q *int) {
	*p, *q = *q, *p
}

// SwapLocals swaps two locals.
//
// @Ensures a = 2 And b = 1
func SwapLocals() (a, b int) {
	a, b = 1, 2
	Swap(&a, &b)
	return a, b
}

// Config has a limit that may be absent.
type Config struct {
	Limit *int
	Name  *string
}

// LimitOr returns the limit of c, or d when it has none.
//
// @Ensures c.Limit != nil -> n = *c.Limit
// @Ensures c.Limit = nil -> n = d
func LimitOr(c Config, d int) (n int) {
	if c.Limit != nil {
		n = *c.Limit
	} else {
		n = d
	}
	return n
}

// SetLimit points c's limit to a new int.
//
// @Requires c != nil
// @Modifies c
// @Ensures c.Limit' != nil And *c.Limit' = n And fresh(c.Limit)
func SetLimit(c *Config, n int) {
	c.Limit = &n
}

// Rename sets what s points to.
//
// @Requires s != nil
// @Modifies s
// @Ensures *s' = v
func Rename(s *string, v string) {
	*s = v
}

// Toggle negates what b points to.
//
// @Requires b != nil
// @Modifies b
// @Ensures *b' != *b
func Toggle(b *bool) {
	*b = !*b
}

// Store stores a float.
//
// @Requires f != nil
// @Modifies f
// @Ensures True
func Store(f *float64, x float64) {
	*f = x
}

// NewInt returns a pointer to a new int.
//
// @Ensures p != nil And fresh(p) And *p = n
func NewInt(n int) (p *int) {
	x := n
	return &x
}

// Counter counts.
type Counter int

// Inc increments the counter.
//
// @Requires c != nil And *c < 100
// @Modifies c
// @Ensures *c' = *c + 1
func (c *Counter) Inc() {
	*c++
}

// CountTwice increments a local counter twice.
//
// @Ensures r = 2
func CountTwice() (r Counter) {
	var k Counter
	k.Inc()
	k.Inc()
	return k
}

// Converted increments through a *int what a *Counter points to.
//
// @Requires c != nil And *c < 100
// @Modifies c
// @Ensures *c' = *c + 1
func Converted(c *Counter) {
	Inc((*int)(c))
}

// DeferredResult increments the named result through a pointer in a
// deferred literal, after the return assigned 1 (F2 of the design review).
//
// @Ensures r = 2
func DeferredResult() (r int) {
	p := &r
	defer func() { *p = *p + 1 }()
	return 1
}

// SwitchedAddress takes the address of the variable of a type switch.
//
// @Ensures x != nil -> True
func SwitchedAddress(x any) (r int) {
	switch v := x.(type) {
	case int:
		p := &v
		*p = 3
		return v
	}
	return 0
}

// pair returns two values.
//
// @Ensures a = 1 And b = 2
func pair() (a, b int) {
	return 1, 2
}

// TwoResults takes the address of a variable declared by a call with two
// results.
//
// @Ensures r = 3
func TwoResults() (r int) {
	x, y := pair()
	p := &x
	*p = *p + y
	return x
}

// Captured writes a variable in a literal called where it is written, and
// reads it through a pointer.
//
// @Ensures r = 4
func Captured() (r int) {
	x := 1
	p := &x
	func() { x = 4 }()
	return *p
}

// Owner owns the counter its field points to.
//
// @Owns c
type Owner struct {
	c *Counter
}

// useOwner writes what p points to and claims that what o owns is
// unchanged, which holds when p is not part of it.
//
// @Requires o != nil And o.c != nil And p != nil And *p < 100
// @Modifies o, p
// @Ensures o.c' = o.c And *o.c' = *o.c
func useOwner(o *Owner, p *int) {
	Inc(p)
	o.c = o.c
}
