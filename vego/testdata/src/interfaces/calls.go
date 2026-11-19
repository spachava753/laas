package interfaces

import "interfaceslib"

// @Requires p != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= total <= 1000000
func Line(p Pricer, sku string, qty int) (total int, ok bool) {
	return p.Price(sku, qty)
}

// @Requires p != nil
// @Ensures ok -> 0 <= total <= 2000000
func Two(p Pricer) (total int, ok bool) {
	a, okA := p.Price("a", 1)
	b, okB := p.Price("b", 2)
	if !okA || !okB {
		return 0, false
	}
	return a + b, true
}

// A call through an interface writes what the Modifies of its method lists
// and nothing else.
//
// @Requires s != nil And c != nil And d != nil And c != d
// @Modifies c.V
// @Ensures c.V' = 7 And d.V' = d.V
func SetOne(s Setter, c *Cell, d *Cell) {
	s.Set(c, 7)
}

// @Requires s != nil And c != nil
// @Modifies c.V
// @Ensures c.V' = 3
func DeferredSet(s Setter, c *Cell) {
	defer s.Set(c, 3)
	c.V = 1
}

// @Requires s != nil And c != nil And d != nil And c != d
// @Requires 0 <= n <= 100
// @Modifies c.V
// @Ensures d.V' = d.V
func SetMany(s Setter, c *Cell, d *Cell, n int) {
	// @Invariant d.V = old(d.V)
	// @Invariant 0 <= i
	// @Variant n - i
	for i := 0; i < n; i++ {
		s.Set(c, i)
	}
}

// @Requires h != nil
// @Ensures True
func FromField(h *Holder) (a int) {
	if h.Shape == nil {
		return 0
	}
	return h.Shape.Area()
}

// @Requires p != nil
// @Ensures True
func OnOneSide(p Pricer, ready bool) (ok bool) {
	if ready {
		_, ok = p.Price("x", 1)
	}
	return ready && ok
}

// @Requires p != nil
// @Ensures True
func InPlace(p Pricer) (n int) {
	price := func(qty int) (cents int) {
		cents, _ = p.Price("y", qty)
		return cents
	}
	return price(3)
}

// @Requires s != nil
// @Ensures 0 <= n <= 100
func OtherPackage(s interfaceslib.Sizer) (n int) {
	return s.Size()
}

// A defined type made from an interface type has its methods, and so their
// contracts.
//
// @Requires s != nil
// @Ensures 0 <= n <= 100
func ThroughDefined(s interfaceslib.Sized) (n int) {
	return s.Size()
}

// @Requires b != nil
// @Ensures 0 <= n <= 100
func Embedded(b Both) (n int) {
	return b.Size()
}

// Visitor is given a pricer.
type Visitor interface {
	// @Requires p != nil
	// @Ensures True
	Visit(p Pricer)
}

// An interface value whose methods all have contracts can be handed to a
// method of another interface value.
//
// @Requires v != nil And p != nil
// @Ensures True
func Visit(v Visitor, p Pricer) {
	v.Visit(p)
}

// Visiting is a function type that is given a pricer.
//
// @Requires p != nil
// @Ensures True
type Visiting func(p Pricer)

// @Requires f != nil And p != nil
// @Ensures True
func VisitWith(f Visiting, p Pricer) {
	f(p)
}
