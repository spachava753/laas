package owns

// Steal stores the array of another stack, which s did not own.
//
// @Requires s != nil And o != nil
// @Modifies s
// @Ensures True
func Steal(s, o *Stack) {
	s.items = o.items // want `vego: s.items may come to refer to memory that existed when Steal was called and that it did not own; an owned field may refer only to memory made since, or to part of what it referred to then`
}

// FromParameter makes a stack over a slice it is handed.
//
// @Ensures r != nil
func FromParameter(xs []int) (r *Stack) {
	return &Stack{items: xs} // want `vego: items of the Stack made here may come to refer to memory that existed when FromParameter was called and that it did not own`
}

// Share makes two stacks of a slice share one array (F1 of the design
// review): the second is new memory, but owned by the first.
//
// @Requires |ss| = 2 And ss[0] != nil And ss[1] != nil
// @Modifies ss[0], ss[1]
// @Ensures True
func Share(ss []*Stack) {
	ss[1].items = make([]int, 1)
	ss[0].items = ss[1].items // want `vego: what is stored into ss\[0\].items is new memory that is not made in this statement`
}

// Pair owns two stacks through pointers.
//
// @Owns p, q
type Pair struct {
	p, q *Stack
}

// Share makes the two stacks of a pair share one array.
//
// @Requires t != nil And t.p != nil And t.q != nil
// @Modifies t
// @Ensures True
func (t *Pair) Share() {
	t.q.items = make([]int, 1)
	t.p.items = t.q.items // want `vego: what is stored into t.p.items is new memory that is not made in this statement`
}

// Held stores new memory held in a variable, which is not supported yet.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Held(c *Cache) {
	m := make(map[string]int)
	m["a"] = 1
	c.m = m // want `vego: what is stored into c.m is new memory that is not made in this statement, and storing such memory into an owned field is not supported yet`
}

// trim returns part of what it is handed.
//
// @Requires |xs| > 0
// @Ensures within(r, xs) And |r| = |xs| - 1
func trim(xs []int) (r []int) {
	return xs[1:]
}

// Trimmed stores what a verified function returns, which is not supported
// until the summaries of what a function keeps.
//
// @Requires s != nil And |s.items| > 0
// @Modifies s
// @Ensures True
func Trimmed(s *Stack) {
	s.items = trim(s.items) // want `vego: what is stored into s.items comes from the call of trim, a verified function; storing the result of such a call into an owned field is not supported yet`
}

// Unlisted writes what s owns without Modifies.
//
// @Requires s != nil And |s.items| > 0
// @Ensures True
func Unlisted(s *Stack) {
	s.items[0] = 1 // want `vego: s.items\[0\] is assigned, which Unlisted may not modify`
}

// id returns what it is handed.
//
// @Ensures within(r, xs) And |r| = |xs|
func id(xs []int) (r []int) {
	return xs
}

// ThroughVerified stores new memory that a verified call handed back,
// which may have kept it: the memory is made in the statement, but not by
// the expression stored.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func ThroughVerified(s *Stack) {
	s.items = id(make([]int, 1)) // want `vego: what is stored into s.items comes from the call of id, a verified function`
}

// AppendOther appends to the array another stack owns, in place: the
// result is new since the function was entered, but not made by the
// append, and two stacks would share it.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func AppendOther(s *Stack) {
	t := &Stack{items: make([]int, 1, 4)}
	s.items = append(t.items, 2) // want `vego: what is stored into s.items is new memory that is not made in this statement`
}
