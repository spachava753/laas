package owns

// Bag owns its slice and holds at most ten items.
//
// @Owns items
// @Invariant |items| <= 10
type Bag struct {
	items []int
	n     int
}

// Box holds two bags by value, and so owns what they own and carries their
// invariants, each at its own offset (F22 of the review of step 2).
type Box struct {
	first  Bag
	second Bag
}

// Bounded reads the second bag's length, which its invariant bounds.
//
// @Requires b != nil
// @Ensures r
func (b *Box) Bounded() (r bool) {
	return len(b.second.items) <= 10
}

// Break gives the second bag eleven items.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func (b *Box) Break() {
	b.second.items = make([]int, 11)
} // want `vego: invariant of Bag may not hold for b on return, in what it owns at second: \|items\| <= 10`

// List has the fields of Stack, so it owns what Stack owns, though it
// declares nothing (F25 of the review of step 2).
type List struct {
	items []int
}

// Set stores a slice it is handed into the field List owns.
//
// @Requires l != nil
// @Modifies l
// @Ensures True
func (l *List) Set(xs []int) {
	l.items = xs // want `vego: l.items may come to refer to memory that existed when Set was called and that it did not own; an owned field may refer only to memory made since, or to part of what it referred to then; copy it into new memory, as slices.Clone does, or, since List owns items because it has the fields of Stack, which declares // @Owns items; give List a field of its own, or use Stack`
}

// CopyList copies a List.
//
// @Requires l != nil
// @Ensures True
func CopyList(l *List) {
	x := *l // want `vego: cannot verify CopyList: \*l copies a value of type List, which owns memory \(List owns items because it has the fields of Stack, which declares // @Owns items; give List a field of its own, or use Stack\)`
	_ = x
}
