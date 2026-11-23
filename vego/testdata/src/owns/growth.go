package owns

// Steal stores the array of another stack, which s did not own.
//
// @Requires s != nil And o != nil
// @Modifies s
// @Ensures True
func Steal(s, o *Stack) {
	s.items = o.items // want `vego: s.items may come to refer to memory that existed when Steal was called and that it did not own; an owned field may refer only to memory made since, or to part of what it referred to then; copy it into new memory, as slices.Clone does, or do not declare the field owned`
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
	ss[0].items = ss[1].items // want `vego: what is stored into ss\[0\].items is new memory that something else may refer to: it is memory that ss\[1\] owns`
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
	t.p.items = t.q.items // want `vego: what is stored into t.p.items is new memory that something else may refer to: it is memory that t owns`
}

// Held stores new memory held in a variable, which nothing else refers to.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Held(c *Cache) {
	m := make(map[string]int)
	m["a"] = 1
	c.m = m
}

// trim returns part of what it is handed.
//
// @Requires |xs| > 0
// @Ensures within(r, xs) And |r| = |xs| - 1
func trim(xs []int) (r []int) {
	return xs[1:]
}

// Trimmed stores what a verified function returns within what it is
// handed, which it keeps nothing of.
//
// @Requires s != nil And |s.items| > 0
// @Modifies s
// @Ensures True
func Trimmed(s *Stack) {
	s.items = trim(s.items)
}

// Unlisted writes what s owns without Modifies.
//
// @Requires s != nil And |s.items| > 0
// @Ensures True
func Unlisted(s *Stack) {
	s.items[0] = 1 // want `vego: s.items\[0\] is assigned, which Unlisted may not modify`
}

// keepIn returns what it is handed, and keeps it in h too.
//
// @Requires h != nil
// @Modifies h
// @Ensures within(r, xs) And |r| = |xs|
func keepIn(h *Holder, xs []int) (r []int) {
	h.data = xs
	return xs
}

// Holder holds a slice it does not own.
type Holder struct {
	data []int
}

// ThroughKeeping stores new memory that a verified call handed back and
// kept in h: the memory is new, but something else refers to it.
//
// @Requires s != nil And h != nil
// @Modifies s, h
// @Ensures True
func ThroughKeeping(s *Stack, h *Holder) {
	s.items = keepIn(h, make([]int, 1)) // want `vego: what is stored into s.items comes from the call of keepIn, a verified function`
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
	s.items = append(t.items, 2) // want `vego: what is stored into s.items is new memory that something else may refer to: it is memory that the Stack made at growth.go:[0-9:]+ owns`
}

// TwoNew stores the array one new stack owns into another (F17 of the
// review of step 1): new memory, but not this statement's, and not within
// what s.items held.
//
// @Ensures True
func TwoNew() {
	s := &Stack{items: make([]int, 2)}
	t := &Stack{items: make([]int, 2)}
	s.items = t.items // want `vego: what is stored into s.items is new memory that something else may refer to: it is memory that the Stack made at growth.go:[0-9:]+ owns; make it where it is stored, as in s.items = make\(...\), or copy it there`
}

// TwoNewServers does the same with the structs two servers own.
//
// @Ensures True
func TwoNewServers() {
	s := &Server{cfg: &Config{}}
	t := &Server{cfg: &Config{}}
	s.cfg = t.cfg // want `vego: what is stored into s.cfg is new memory that something else may refer to: it is memory that the Server made at growth.go:[0-9:]+ owns; make it where it is stored, as in s.cfg = &Config\{...\}, or copy it there`
}

// LocalValue stores a parameter's slice into a local owner, which is
// refused once: what follows is verified as if the store were allowed.
//
// @Requires |xs| < 10
// @Ensures True
func LocalValue(xs []int) {
	var st Stack
	st.items = xs // want `vego: st.items may come to refer to memory that existed when LocalValue was called`
	st.Push(1)
}
