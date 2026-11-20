package guide

// Reserve returns an empty slice with room for n elements.
//
// @Requires 0 <= n <= 1000
// @Ensures |r| = 0 And cap(r) = n And r != nil
func Reserve(n int) (r []int) {
	return make([]int, 0, n)
}

// @Ensures r != nil
func EmptyOf(A []int) (r []int) {
	return A[:0] // want `postcondition may not hold: r != nil`
}

// Halves holds two slices that the type does not keep apart.
type Halves struct {
	front, back []int
}

// @Requires h != nil And |h.front| > 0 And |h.back| > 0 And apart(h.front, h.back)
// @Modifies h.front
// @Ensures h.front'[0] = 0 And h.back'[0] = h.back[0]
func ClearFront(h *Halves) {
	h.front[0] = 0
}

// @Requires h != nil And |h.front| > 0 And |h.back| > 0
// @Modifies h.front
// @Ensures h.back'[0] = h.back[0]
func ClearFrontWrong(h *Halves) {
	h.front[0] = 0
} // want `postcondition may not hold: h.back'\[0\] = h.back\[0\]`

// Item is an element of a Ring, whose root marks where it starts.
type Item struct {
	next *Item
	ring *Ring
}

// Ring is a list that ends at its own root.
type Ring struct {
	root Item
	size int
}

// Next returns the item after e, or nil at the end of the ring.
//
// @Requires e != nil
// @Ensures result = nil <-> (e.ring = nil Or e.next = nil Or e.next = &e.ring.root)
// @Ensures result != nil -> result = e.next
func (e *Item) Next() (result *Item) {
	if p := e.next; e.ring != nil && p != &e.ring.root {
		return p
	}
	return nil
}
