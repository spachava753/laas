package guide

import "fmt"

// The programs of the section on interfaces.

// Pricer prices an order line.
type Pricer interface {
	// Price returns the price in cents of qty units of sku, and whether
	// sku is known.
	//
	// @Requires 0 <= qty <= 1000
	// @Ensures ok -> 0 <= cents <= 1000000
	Price(sku string, qty int) (cents int, ok bool)
}

// LinesTotal adds the prices of two lines.
//
// @Requires p != nil
// @Requires 0 <= a <= 1000 And 0 <= b <= 1000
// @Ensures ok -> 0 <= total <= 2000000
func LinesTotal(p Pricer, a, b int) (total int, ok bool) {
	x, okA := p.Price("apple", a)
	y, okB := p.Price("pear", b)
	if !okA || !okB {
		return 0, false
	}
	return x + y, true
}

// @Ensures True
func TotalOfNil(p Pricer) (total int, ok bool) {
	return p.Price("apple", 1) // want `the interface value p may be nil`
}

// Table prices every item at the same rate.
type Table struct {
	Rate int
}

// Price uses the rate of the table.
//
// @Requires t != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (t *Table) Price(sku string, qty int) (cents int, ok bool) {
	if t.Rate < 0 || t.Rate > 1000 {
		return 0, false
	}
	return t.Rate * qty, true
}

// @Requires t != nil
// @Ensures ok -> 0 <= total <= 2000000
func TotalAtRate(t *Table) (total int, ok bool) {
	return LinesTotal(t, 1, 2)
}

// Flat prices every item at 2000 cents.
type Flat struct{}

// @Requires 0 <= qty <= 1000
// @Ensures ok
func (Flat) Price(sku string, qty int) (cents int, ok bool) {
	return 2000 * qty, true
}

// @Ensures p != nil
func FlatPricer() (p Pricer) {
	return Flat{} // want `postcondition may not hold: ok -> 0 <= cents <= 1000000, in Flat.Price used as a method of Pricer at interfaces.go:\d+:\d+`
}

// LineCounter counts the lines it prices.
type LineCounter struct {
	lines int
}

// @Requires c != nil And 0 <= qty <= 1000
// @Modifies c
// @Ensures ok -> 0 <= cents <= 1000000
func (c *LineCounter) Price(sku string, qty int) (cents int, ok bool) {
	if c.lines < 1000 {
		c.lines++
	}
	return 0, true
}

// @Requires c != nil
// @Ensures p != nil
func CountingPricer(c *LineCounter) (p Pricer) {
	return c // want `Price may modify c, which Pricer.Price may not modify; Pricer.Price can list only what its parameters refer to, so a method that writes what its receiver refers to cannot be used as a method of Pricer yet, in \(\*LineCounter\).Price used as a method of Pricer at interfaces.go:\d+:\d+`
}

// Rated has a value receiver.
type Rated struct {
	Rate int
}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (r Rated) Price(sku string, qty int) (cents int, ok bool) {
	if r.Rate < 0 || r.Rate > 1000 {
		return 0, false
	}
	return r.Rate * qty, true
}

// @Ensures p != nil
func RatedPricer(r *Rated) (p Pricer) {
	return r // want `Rated.Price has a value receiver, and the pointer that the interface value holds may be nil, in Rated.Price used as a method of Pricer at interfaces.go:\d+:\d+`
}

// Sized has a method of its own.
type Sized interface {
	// @Ensures n >= 0
	Size() (n int)
}

// Catalog is a pricer that also reports a size.
type Catalog interface {
	Pricer
	Sized
}

// @Ensures (p = nil) <-> (c = nil)
func AsPricer(c Catalog) (p Pricer) {
	return c
}

// @Ensures (a = nil) <-> (p = nil)
func AsAny(p Pricer) (a any) {
	return p
}

// @Ensures same
func SamePricer(p, q Pricer) (same bool) {
	return p == q // want `vego: p == q may panic: p and q may hold values of one type on which == panics, such as a slice or a struct that holds one; say what they hold, as a contract does with holds\(p, T\), or assert them first` `postcondition may not hold: same`
}

// Logging wraps a pricer.
type Logging struct {
	Inner Pricer
}

// @Requires l.Inner != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (l Logging) Price(sku string, qty int) (cents int, ok bool) {
	return l.Inner.Price(sku, qty) // want `this call may not end: Logging.Price calls l.Inner.Price\(sku, qty\) at interfaces.go:\d+:\d+, which may run Logging.Price`
}

// @Requires inner != nil
// @Ensures p != nil
func LoggedPricer(inner Pricer) (p Pricer) {
	return Logging{Inner: inner} // want `cannot verify LoggedPricer: Price may call through a function value or an interface value, and code that an interface value runs cannot do that yet: no contract of a function type or of a method of an interface has a variant, so nothing would prove that such calls end`
}

// RatedLogging wraps a Rated, a concrete type, and so calls its method
// statically.
type RatedLogging struct {
	Inner Rated
}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (l RatedLogging) Price(sku string, qty int) (cents int, ok bool) {
	return l.Inner.Price(sku, qty)
}

// @Ensures p != nil
func LoggedRated(inner Rated) (p Pricer) {
	return RatedLogging{Inner: inner}
}

// @Requires s != nil
// @Ensures True
func Show(s fmt.Stringer) (text string) {
	return s.String() // want `cannot verify Show: s.String calls Stringer.String, which has no contract; a method of an interface gets one in its doc comment where the interface is declared, with // @ annotations; for a type of another module, give it an entry \(fmt.Stringer\).String in vego-trusted.yaml`
}

// Bounded declares a Size of its own.
type Bounded interface {
	// @Ensures n <= 100
	Size() (n int)
}

// Measured gets Size from both.
type Measured interface { // want `the contract of Bounded.Size is not part of this interface: it has Size from Sized.Size, and Go keeps one declaration of a method; declare the method once, with its contract`
	Sized
	Bounded
}
