// Package invariants holds struct types with invariants and functions that
// keep or break them.
package invariants

import "shapes"

// Stack keeps a count that never exceeds what it holds.
//
// @ Invariant 0 <= n <= |items|
type Stack struct {
	items []int
	n     int
}

// Top relies on the invariant to index safely.
//
// @ Requires s != nil And s.n > 0
// @ Ensures result = s.items[s.n - 1]
func (s *Stack) Top() (result int) {
	return s.items[s.n-1]
}

// Drop keeps the invariant.
//
// @ Requires s != nil And s.n > 0
// @ Modifies s.n
// @ Ensures s.n' = s.n - 1
func (s *Stack) Drop() {
	s.n--
}

// Grow breaks the invariant: the count may run past the items.
//
// @ Requires s != nil And s.n < 1000
// @ Modifies s.n
func (s *Stack) Grow() {
	s.n++
} // want `vego: invariant of Stack may not hold for s on return: 0 <= n <= \|items\|`

// DropTwice may break the invariant between its calls, but not across them.
//
// @ Requires s != nil And s.n > 1
// @ Modifies s.n
// @ Ensures s.n' = s.n - 2
func DropTwice(s *Stack) {
	s.Drop()
	s.Drop()
}

// BreaksBeforeCall passes a stack whose invariant it has broken.
//
// @ Requires s != nil And s.n > 0
// @ Modifies s.n
func BreaksBeforeCall(s *Stack) {
	s.n = -1
	s.Drop() // want `vego: invariant of Stack may not hold for what is passed to Drop as s: 0 <= n <= \|items\|`
	s.n = 0
}

// RestoresBeforeReturn breaks the invariant in between, which is allowed.
//
// @ Requires s != nil
// @ Modifies s.n
// @ Ensures s.n' = s.n
func RestoresBeforeReturn(s *Stack) {
	saved := s.n
	s.n = -5
	s.n = saved
}

// NewStack has to establish the invariant of its result.
//
// @ Ensures fresh(result) And result.n = 0
func NewStack() (result *Stack) {
	return &Stack{}
}

// BadStack returns a stack that claims an element it does not have.
//
// @ Ensures fresh(result)
func BadStack() (result *Stack) {
	return &Stack{n: 1} // want `vego: invariant of Stack may not hold for the result: 0 <= n <= \|items\|`
}

// ByValue takes a stack by value; the invariant holds of the copy.
//
// @ Ensures True
func ByValue(s Stack) (result int) {
	if s.n > 0 {
		return s.items[s.n-1]
	}
	return 0
}

// ReturnsValue returns a struct value, which must meet the invariant too.
//
// @ Ensures True
func ReturnsValue() (result Stack) {
	return Stack{n: 3} // want `vego: invariant of Stack may not hold for the result: 0 <= n <= \|items\|`
}

// Nil may be passed where a pointer is expected: there is nothing the
// invariant could be about.
//
// @ Ensures result = 0
func Nil() (result int) {
	var s *Stack
	return count(s)
}

// count tolerates nil.
//
// @ Ensures s = nil -> result = 0
// @ Ensures s != nil -> 0 <= result <= |s.items|
func count(s *Stack) (result int) {
	if s == nil {
		return 0
	}
	return s.n
}

// Impossible has invariants no value can meet.
//
// @ Invariant x > 0 // want `vego: the invariants of Impossible contradict each other, so no value of the type could exist`
// @ Invariant x < 0
type Impossible struct{ x int }

// Misnamed has an invariant about a field that is not there.
//
// @ Invariant y > 0 // want `vego: in Invariant annotation: y is neither a field of the type nor a constant`
type Misnamed struct{ x int }

// Primed has an invariant that speaks of two states.
//
// @ Invariant x' > 0 // want `vego: in Invariant annotation: an invariant describes one state, so x cannot be primed or put in old\(\)`
type Primed struct{ x int }

// Number is not a struct.
//
// @ Invariant True // want `vego: an Invariant can only be declared on a struct type without type parameters`
type Number int

// Wrong carries an annotation that does not belong on a type.
//
// @ Requires x > 0 // want `vego: Requires annotations do not belong on a type; a type can only have Invariant annotations`
type Wrong struct{ x int }

// Square uses the invariant of a type of another package, with that
// package's constant.
//
// @ Requires r != nil
// @ Ensures 0 <= result <= 10000
func Square(r *shapes.Rect) (result int) {
	return r.W * r.W
}

// Widen breaks the invariant of a type of another package.
//
// @ Requires r != nil
// @ Modifies r.W
func Widen(r *shapes.Rect) {
	r.W = 101
} // want `vego: invariant of Rect may not hold for r on return: 0 <= W <= Limit`

// UsesNew gets a rectangle whose invariant its maker proved.
//
// @ Ensures 0 <= result <= 10000
func UsesNew() (result int) {
	r := shapes.New(3, 4)
	return r.Area()
}

// Log stands for a type whose method is trusted.
//
// @ Invariant count >= 0
type Log struct{ count int }

func (l *Log) write() {}

// AfterTrusted cannot assume the invariant after a trusted call that may
// have changed the struct, since nobody proved it.
//
// @ Requires l != nil
// @ Modifies l
func AfterTrusted(l *Log) {
	l.write()
} // want `vego: invariant of Log may not hold for l on return: count >= 0`

// Cell is a struct another struct points to.
type Cell struct{ x int }

// Holder says something about what it points to.
//
// @ Invariant p != nil And p.x = 0
type Holder struct{ p *Cell }

// BreaksThroughCopy gets its struct by value, but what the struct points to
// is the caller's.
//
// @ Modifies h.p.x
func BreaksThroughCopy(h Holder) {
	h.p.x = 1
} // want `vego: invariant of Holder may not hold for h on return: p.x = 0`

// KeepsThroughCopy changes its copy only.
//
// @ Ensures result = 0
func KeepsThroughCopy(h Holder) (result int) {
	h.p = nil
	return 0
}

// Tagged has a field of a type the verifier does not model, with the name
// of a built-in limit.
//
// @ Invariant MaxInt8 = 127 // want `vego: in Invariant annotation: MaxInt8 has type uintptr, which is not supported`
type Tagged struct {
	MaxInt8 uintptr
	X       int
}

// MakesTagged cannot be verified, since the invariant of its result cannot
// be read.
//
// @ Ensures True
func MakesTagged() (result Tagged) { // want `vego: cannot verify MakesTagged: the invariants of Tagged could not be understood`
	return Tagged{}
}

// MakesBroken uses a type of another package whose invariant cannot be read.
//
// @ Ensures True
func MakesBroken() (result shapes.Broken) { // want `vego: cannot verify MakesBroken: the invariants of Broken could not be understood`
	return shapes.Broken{X: 99}
}

// TakesNever takes a value of a type whose invariants contradict each other.
//
// @ Ensures result = 0
func TakesNever(n shapes.Never) (result int) { // want `vego: cannot verify TakesNever: the invariants of Never could not be understood`
	return 1
}
