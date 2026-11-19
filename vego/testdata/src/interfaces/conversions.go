package interfaces

// Table prices from a fixed rate.
type Table struct {
	Rate int
}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (t *Table) Price(sku string, qty int) (cents int, ok bool) {
	return qty * 1000, true
}

// Flat prices everything the same, by value.
type Flat int

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (f Flat) Price(sku string, qty int) (cents int, ok bool) {
	if f < 0 || f > 1000 {
		return 0, false
	}
	return int(f) * qty, true
}

// @Requires t != nil
// @Ensures p != nil
func FromPointer(t *Table) (p Pricer) {
	return t
}

// A nil pointer in an interface makes an interface value that is not nil,
// and a method that does not read through the receiver can run on it.
//
// @Ensures p != nil
func FromNilPointer() (p Pricer) {
	var t *Table
	p = t
	return p
}

// @Ensures p != nil
func FromValue(f Flat) (p Pricer) {
	return f
}

// @Ensures p != nil
func FromConstant() (p Pricer) {
	return Flat(3)
}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= total <= 1000000
func Converted(t *Table, qty int) (total int, ok bool) {
	return Line(t, "a", qty)
}

// @Ensures True
func Explicit(f Flat) (ok bool) {
	p := Pricer(f)
	_, ok = p.Price("a", 1)
	return ok
}

// @Ensures |ps| = 2
func InSlice(f Flat, t *Table) (ps []Pricer) {
	return []Pricer{f, t}
}

// @Ensures True
func InMap(f Flat) (m map[string]Pricer) {
	m = map[string]Pricer{}
	m["f"] = f
	return m
}

type Shop struct {
	Pricer Pricer
	Name   string
}

// @Ensures s.Pricer != nil
func InStruct(f Flat) (s Shop) {
	return Shop{Pricer: f, Name: "x"}
}

// @Requires s != nil
// @Modifies s
// @Ensures s.Pricer' != nil
func IntoField(s *Shop, f Flat) {
	s.Pricer = f
}

// @Ensures |ps| = 1
func Appended(f Flat) (ps []Pricer) {
	ps = append(ps, f)
	return ps
}

// @Ensures a != nil
func ToAny(t *Table) (a any) {
	return t
}

// One value is evaluated where it is not converted and where it is, so the
// list of conversions has to name the expression that is converted, and
// not another expression of the same value.
//
// @Ensures True
func Reused(f Flat) (n int) {
	same(f)
	_, _ = Line(f, "a", 1)
	x := f
	_, _ = Line(x, "b", 2)
	_ = both(f, x)
	return int(same(x))
}

// @Ensures g = f
func same(f Flat) (g Flat) {
	return f
}

// @Ensures True
func Twice(f Flat) (n int) {
	return both(f, f)
}

// @Requires p != nil And q != nil
// @Ensures True
func both(p Pricer, q Pricer) (n int) {
	return 0
}
