package smalls

// Two interface values are the same value when one was copied from the
// other. That is not Go's ==.

// Ring is a node of a ring with a value of any type.
type Ring struct {
	next, prev *Ring
	Value      any
}

// @Requires r != nil
// @Modifies r
// @Ensures r.next' = r And r.prev' = r And r.Value' = r.Value
func (r *Ring) init() {
	r.next = r
	r.prev = r
}

// @Requires r != nil
// @Modifies r
// @Ensures r.Value' = r.Value
func (r *Ring) clear() {
	r.Value = nil
} // want `postcondition may not hold: r.Value' = r.Value`

// @Requires a != nil And b != nil And a != b
// @Modifies a, b
// @Ensures a.Value' = b.Value And b.Value' = a.Value
func Swap(a, b *Ring) {
	a.Value, b.Value = b.Value, a.Value
}

// @Ensures y = x
func Keep(x any) (y any) {
	return x
}

// A conversion between interfaces keeps the value.

// Sink takes values.
type Sink interface {
	// @Ensures True
	Put(v int)
}

// @Ensures a = s
func Widen(s Sink) (a any) {
	return s
}

// Two conversions of one pointer are two values, although == on them in
// Go is true.

// @Requires p != nil
// @Ensures a != b
func Twice(p *Node) (a, b any) {
	return p, p
}

// @Requires p != nil
// @Ensures a = b
func TwiceSame(p *Node) (a, b any) {
	return p, p // want `postcondition may not hold: a = b`
}

// A contract of a type may relate two interface values, and a value of
// the type meets it.

// Echo hands back what it is given.
type Echo interface {
	// @Ensures r = x
	Echo(x Sink) (r Sink)
}

// echo is an Echo, checked against the contract where MakeEcho converts
// it.
type echo struct{}

// @Ensures r = x
func (echo) Echo(x Sink) (r Sink) {
	return x
}

// @Ensures e != nil
func MakeEcho() (e Echo) {
	return echo{}
}

// An error and an interface value of another type have different models.

// @Ensures x = err // want `in Ensures annotation: cannot compare x \(interface value\) with err \(error\)`
func WithError(x any, err error) {
}

// lose is converted to an Echo whose contract it does not meet.
type lose struct{}

// @Ensures r = nil
func (lose) Echo(x Sink) (r Sink) {
	return nil
}

// @Ensures e != nil
func MakeLose() (e Echo) {
	return lose{} // want `postcondition may not hold: r = x, in lose.Echo used as a method of Echo`
}
