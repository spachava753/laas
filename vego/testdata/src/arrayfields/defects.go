package arrayfields

// Wrong claims that writing the first item changed the next.
//
// @Requires |xs| > 1
// @Modifies xs
// @Ensures xs'[1].Vals[2] = 5
func Wrong(xs []Item) {
	xs[0].Vals[2] = 5
} // want `vego: postcondition may not hold: xs'\[1\]\.Vals\[2\] = 5`

// Bad writes the next item through a slice of its field and claims it kept.
//
// @Requires |xs| > 1
// @Modifies xs
// @Ensures xs'[1].Vals[0] = xs[1].Vals[0]
func Bad(xs []Item) {
	s := xs[1].Vals[:]
	s[0] = 4
} // want `vego: postcondition may not hold: xs'\[1\]\.Vals\[0\] = xs\[1\]\.Vals\[0\]`

// CallerWrong claims that set kept what it wrote; with F36's floor the
// call did not forget that element, and the claim verified (the prototype
// of step 3a).
//
// @Requires |xs| > 2 And xs[1].Vals[1] = 8
// @Modifies xs
// @Ensures xs'[1].Vals[1] = 8
func CallerWrong(xs []Item) {
	set(xs[1:])
} // want `vego: postcondition may not hold: xs'\[1\]\.Vals\[1\] = 8`

// LoopWrong claims the tail kept a value the loop zeroed.
//
// @Requires |xs| > 2 And xs[1].Vals[3] = 5
// @Modifies xs
// @Ensures xs'[1].Vals[3] = 5
func LoopWrong(xs []Item) {
	t := xs[1:]
	// @Invariant True
	for i := range t {
		t[i].Vals[3] = 0
	}
} // want `vego: postcondition may not hold: xs'\[1\]\.Vals\[3\] = 5`

// PtrWrong claims a write through a pointer kept the element.
//
// @Requires |xs| > 2 And xs[1].Vals[2] = 5
// @Modifies xs
// @Ensures xs'[1].Vals[2] = 5
func PtrWrong(xs []Item) {
	zero(&xs[1].Vals[2])
} // want `vego: postcondition may not hold: xs'\[1\]\.Vals\[2\] = 5`

// NextChanged claims that zero, handed the first element, changed the
// second: a pointer to an element covers one position, not its eight
// bytes.
//
// @Requires w != nil And w.Arr[1] = 3
// @Modifies w.Arr
// @Ensures w.Arr'[1] = 0
func NextChanged(w *Wide) {
	zero(&w.Arr[0])
} // want `vego: postcondition may not hold: w\.Arr'\[1\] = 0`

// SecondWithin claims that the second element lies within the slice of
// the first.
//
// @Requires w != nil
// @Ensures True
func SecondWithin(w *Wide) {
	p, s := &w.Arr[1], w.Arr[:1:1]
	// @Assert within(p, s) // want `vego: assertion may not hold: within\(p, s\)`
	_, _ = p, s
}

// SecondHalfZero claims that zeroing the first half zeroed the second.
//
// @Requires w != nil And w.Arr[2] = 1
// @Modifies w.Arr
// @Ensures w.Arr'[2] = 0
func SecondHalfZero(w *Wide) {
	s := w.Arr[:2:2]
	// @Invariant True
	for i := range s {
		s[i] = 0
	}
} // want `vego: postcondition may not hold: w\.Arr'\[2\] = 0`

// PlaceChangedElement claims that writing s.B changed s.C[0].
//
// @Requires s != nil And s.C[0] = 5
// @Modifies s.B
// @Ensures s.C'[0] = 1
func PlaceChangedElement(s *Shorts) {
	setFirst(&s.B, &s.C[0])
} // want `vego: postcondition may not hold: s\.C'\[0\] = 1`

// ElementChangedPlace claims that writing s.C[0] changed s.B.
//
// @Requires s != nil And s.B = 5
// @Modifies s.C
// @Ensures s.B' = 1
func ElementChangedPlace(s *Shorts) {
	setFirst(&s.C[0], &s.B)
} // want `vego: postcondition may not hold: s\.B' = 1`

// keepsWithout keeps what q points to without requiring it apart from p,
// which it may be.
//
// @Requires p != nil And q != nil
// @Modifies p
// @Ensures *q' = *q
func keepsWithout(p, q *int16) {
	*p = 1
} // want `vego: postcondition may not hold: \*q' = \*q`

// Counter counts into an array, and its method writes behind its receiver.
type Counter struct {
	N    int64
	Hits [4]int64
}

// Hitter hits.
type Hitter interface {
	// @Receiver h
	// @Modifies h
	// @Ensures True
	Hit()
}

// Hit counts a hit.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func (c *Counter) Hit() {
	c.Hits[0] = 1
}

// ConvertedRun converts a counter and reads an element of its array after
// a call: each element of the run is a leaf of the struct's footprint
// (leafOnly), so nothing is a contradiction.
//
// @Ensures False
func ConvertedRun() {
	c := &Counter{}
	var h Hitter = c
	h.Hit()
	_ = c.Hits[2]
} // want `vego: postcondition may not hold: False`

// WritesWithin writes through a pointer that may point to a place or an
// element of s, and claims the element unchanged.
//
// @Requires s != nil And within(p, s) And s.C[0] = 5
// @Modifies s
// @Ensures s.C'[0] = 5
func WritesWithin(s *Shorts, p *int16) {
	*p = 3
} // want `vego: postcondition may not hold: s\.C'\[0\] = 5`

// H is a number with a method that writes it.
type H int16

// Reset sets h to zero.
//
// @Requires h != nil
// @Modifies h
// @Ensures *h' = 0
func (h *H) Reset() {
	*h = 0
}

// Resetter resets what it holds.
type Resetter interface {
	// @Receiver r
	// @Modifies r
	// @Ensures True
	Reset()
}

// Hs puts the place B at 2 and the element C[0] at the floor 4/2 = 2.
type Hs struct {
	A, B H
	C    [4]H
}

// ConvertedElementKept converts a pointer to an element of a run, calls
// through it, and claims the element kept, which is false. Z3 refutes it
// only past the default limit (F22 of the review of step 3a; ROADMAP, The
// prover), so the note may stand.
//
// @Requires s != nil And s.C[0] = 5
// @Modifies s
// @Ensures s.C'[0] = 5
func ConvertedElementKept(s *Hs) {
	var r Resetter = &s.C[0]
	r.Reset()
} // want `vego: postcondition may not hold: s\.C'\[0\] = 5`
