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
func (s *Stack) Top() int {
	return s.items[s.n-1]
}

//@ Ensures result = s.items[s.n - 1]

// Drop keeps the invariant.
//
// @ Requires s != nil And s.n > 0
// @ Modifies s.n
func (s *Stack) Drop() {
	s.n--
}

//@ Ensures s.n' = s.n - 1

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
func DropTwice(s *Stack) {
	s.Drop()
	s.Drop()
}

//@ Ensures s.n' = s.n - 2

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
func RestoresBeforeReturn(s *Stack) {
	saved := s.n
	s.n = -5
	s.n = saved
}

//@ Ensures s.n' = s.n

// NewStack has to establish the invariant of its result.
func NewStack() *Stack {
	return &Stack{}
}

//@ Ensures fresh(result) And result.n = 0

// BadStack returns a stack that claims an element it does not have.
func BadStack() *Stack {
	return &Stack{n: 1} // want `vego: invariant of Stack may not hold for the result: 0 <= n <= \|items\|`
}

//@ Ensures fresh(result)

// ByValue takes a stack by value; the invariant holds of the copy.
func ByValue(s Stack) int {
	if s.n > 0 {
		return s.items[s.n-1]
	}
	return 0
}

//@ Ensures True

// ReturnsValue returns a struct value, which must meet the invariant too.
func ReturnsValue() Stack {
	return Stack{n: 3} // want `vego: invariant of Stack may not hold for the result: 0 <= n <= \|items\|`
}

//@ Ensures True

// Nil may be passed where a pointer is expected: there is nothing the
// invariant could be about.
func Nil() int {
	var s *Stack
	return count(s)
}

//@ Ensures result = 0

// count tolerates nil.
func count(s *Stack) int {
	if s == nil {
		return 0
	}
	return s.n
}

//@ Ensures s = nil -> result = 0
//@ Ensures s != nil -> 0 <= result <= |s.items|

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
func Square(r *shapes.Rect) int {
	return r.W * r.W
}

//@ Ensures 0 <= result <= 10000

// Widen breaks the invariant of a type of another package.
//
// @ Requires r != nil
// @ Modifies r.W
func Widen(r *shapes.Rect) {
	r.W = 101
} // want `vego: invariant of Rect may not hold for r on return: 0 <= W <= Limit`

// UsesNew gets a rectangle whose invariant its maker proved.
func UsesNew() int {
	r := shapes.New(3, 4)
	return r.Area()
}

//@ Ensures 0 <= result <= 10000

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
