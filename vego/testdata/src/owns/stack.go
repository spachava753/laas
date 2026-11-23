// Package owns holds the programs of ownership declared in source: a
// struct that owns the array of its slice, its map, or the struct a
// pointer field points to (F27).
package owns

import "slices"

// Stack owns the array of its slice, so Modifies s covers it, and items may
// come to refer only to memory made since the method was called or to part
// of what it referred to just before.
//
// @Owns items
type Stack struct {
	items []int
}

// Push appends x: the append writes inside the array s owns, or moves it to
// new memory.
//
// @Requires s != nil And |s.items| < 1000000
// @Modifies s
// @Ensures |s.items'| = |s.items| + 1 And s.items'[|s.items|] = x
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
}

// Pop removes the last element, keeping the array.
//
// @Requires s != nil And |s.items| > 0
// @Modifies s
// @Ensures |s.items'| = |s.items| - 1 And x = s.items[|s.items| - 1]
func (s *Stack) Pop() (x int) {
	x = s.items[len(s.items)-1]
	s.items = s.items[:len(s.items)-1]
	return x
}

// Delete removes the element at i with slices.Delete, whose result lies
// within its argument and which keeps nothing it is handed.
//
// @Requires s != nil And 0 <= i < |s.items|
// @Modifies s
// @Ensures |s.items'| = |s.items| - 1
func (s *Stack) Delete(i int) {
	s.items = slices.Delete(s.items, i, i+1)
}

// Reserve grows the capacity with slices.Grow, whose result is new or
// lies within its argument.
//
// @Requires s != nil And 0 <= n <= 1000000 And |s.items| <= 1000000
// @Modifies s
// @Ensures |s.items'| = |s.items|
func (s *Stack) Reserve(n int) {
	s.items = slices.Grow(s.items, n)
}

// Clip drops the capacity past the length.
//
// @Requires s != nil
// @Modifies s
// @Ensures |s.items'| = |s.items|
func (s *Stack) Clip() {
	s.items = slices.Clip(s.items)
}

// Reset gives the stack a new array.
//
// @Requires s != nil
// @Modifies s
// @Ensures |s.items'| = 0
func (s *Stack) Reset() {
	s.items = make([]int, 0, 8)
}

// Two pushes twice onto a stack it made, with no Modifies: after the first
// Push, what s owns is still new.
//
// @Ensures True
func Two() {
	s := &Stack{}
	s.Push(1)
	s.Push(2)
}

// PushTwo pushes twice onto a stack it is handed, under Modifies s alone.
//
// @Requires s != nil And |s.items| < 1000
// @Modifies s
// @Ensures |s.items'| = |s.items| + 2
func PushTwo(s *Stack) {
	s.Push(1)
	s.Push(2)
}

// Fill pushes in a loop; at the loop's head what s owns is still placed.
//
// @Requires s != nil And |s.items| = 0 And 0 <= n <= 1000
// @Modifies s
// @Ensures |s.items'| = n
func Fill(s *Stack, n int) {
	// @Invariant 0 <= i <= n And |s.items| = i
	// @Variant n - i
	for i := 0; i < n; i++ {
		s.items = append(s.items, i)
	}
}

// Overwrite writes the elements of what s owns directly.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Overwrite(s *Stack) {
	for i := range s.items {
		s.items[i] = 0
	}
}

// Made builds a stack from new memory in a literal.
//
// @Ensures r != nil And |r.items| = 3
func Made() (r *Stack) {
	return &Stack{items: make([]int, 3)}
}

// LoopReplaces gives the stack a new array in each iteration, so the loop
// does not keep it.
//
// @Requires s != nil And 0 <= n <= 10
// @Modifies s
// @Ensures |s.items'| = |s.items|
func LoopReplaces(s *Stack, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		s.items = make([]int, 1)
	}
} // want `vego: postcondition may not hold: \|s.items'\| = \|s.items\|`

// FillInner pushes in a loop onto the stack a pair owns through a pointer:
// at the head what the pair owns is still placed, through p.
//
// @Requires t != nil And t.p != nil And |t.p.items| = 0 And 0 <= n <= 1000
// @Modifies t
// @Ensures |t.p'.items'| = n
func FillInner(t *Pair, n int) {
	// @Invariant 0 <= i <= n And |t.p.items| = i
	// @Variant n - i
	for i := 0; i < n; i++ {
		t.p.items = append(t.p.items, i)
	}
}
