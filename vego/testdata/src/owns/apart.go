package owns

// The separation C3 assumes of what a listed owner owns (F27, step 3b).

// CopyFirst writes what s owns and reads a slice it is handed after: the
// slice is not part of what s owns.
//
// @Requires s != nil And |s.items| > 0 And |xs| > 0
// @Modifies s
// @Ensures xs'[0] = xs[0]
func CopyFirst(s *Stack, xs []int) {
	s.items[0] = 7
}

// PushAll pushes what xs holds, which stays as it was while s grows.
//
// @Requires s != nil And |s.items| + |xs| < 1000000
// @Modifies s
// @Ensures |s.items'| = |s.items| + |xs|
func (s *Stack) PushAll(xs []int) {
	// @Invariant 0 <= i <= |xs| And |s.items| = |old(s.items)| + i
	for i := range xs {
		s.items = append(s.items, xs[i])
	}
}

// Keeps writes what s owns and reads a Config it is handed through a
// pointer: the Config is not what s owns either.
//
// @Requires s != nil And s.cfg != nil And c != nil
// @Modifies s
// @Ensures c.port' = c.port
func Keeps(s *Server, c *Config) {
	s.cfg.port = 1
}

// helper writes a slice it is handed.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func helper(xs []int, n int) {
	xs[0] = n
}

// Helped hands what s owns to a helper that keeps nothing of it, with no
// owner beside it (R6).
//
// @Requires s != nil And |s.items| > 0
// @Modifies s
// @Ensures True
func Helped(s *Stack) {
	helper(s.items, 3)
}

// helper2 writes what s owns and reads xs, which it assumes is not.
//
// @Requires s != nil And |s.items| > 0 And |xs| > 0
// @Modifies s
// @Ensures xs'[0] = xs[0]
func helper2(xs []int, s *Stack) {
	s.items[0] = 7
}

// Beside hands what s owns beside s (R6).
//
// @Requires s != nil And |s.items| > 0
// @Modifies s
// @Ensures True
func Beside(s *Stack) {
	helper2(s.items, s) // want `vego: s.items is memory that s owns, and helper2 is handed what reaches a Stack, which can own it`
}

// Tree owns the slice of its children, which may point back at it.
//
// @Owns kids
type Tree struct {
	kids []*Tree
}

// first hands its slice and its first element on.
//
// @Requires |xs| > 0 And xs[0] != nil
// @Modifies xs[0]
// @Ensures True
func first(xs []*Tree) {
	reset(xs[0], xs)
}

// reset clears what t owns.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func reset(t *Tree, xs []*Tree) {
	t.kids = nil
}

// SelfOwned hands what a tree owns, alone, to a function whose own
// parameter reaches the tree (F2 of the design review).
//
// @Ensures True
func SelfOwned() {
	s := &Tree{}
	s.kids = []*Tree{s}
	first(s.kids) // want `vego: s.kids is memory that the Tree made at apart.go:[0-9:]+ owns, and first is handed what reaches a Tree, which can own it`
}

// CutNeeded writes what s owns through a call and reads it after, with a
// postcondition that is false: the separation must not follow the owned
// cell of s's own struct into what s owns, or it would contradict itself.
//
// @Requires s != nil And |s.items| > 0 And |s.items| < 1000 And |xs| > 0
// @Modifies s
// @Ensures s.items'[0] = 99
func CutNeeded(s *Stack, xs []int) {
	s.Push(xs[0])
	_ = s.items[0]
} // want `vego: postcondition may not hold: s.items'\[0\] = 99`
