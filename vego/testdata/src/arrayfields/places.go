package arrayfields

// Under the floor a place and an element can share a position: in Shorts,
// b is the place at 2 and c[0] the element at ⌊4/2⌋ = 2. A pointer says
// which of the two it points to by #arr, which every check compares beside
// the position (condition 1 of the ruling on step 3a).
type Shorts struct {
	A, B int16
	C    [4]int16
}

// setFirst writes what p points to.
//
// @Requires p != nil And q != nil
// @Modifies p
// @Ensures *p' = 1
func setFirst(p, q *int16) {
	*p = 1
}

// PlaceKeepsElement writes s.B through a pointer and keeps s.C[0], which
// lies at the same position in another region.
//
// @Requires s != nil
// @Modifies s.B
// @Ensures s.B' = 1 And s.C'[0] = s.C[0]
func PlaceKeepsElement(s *Shorts) {
	setFirst(&s.B, &s.C[0])
}

// ElementKeepsPlace writes s.C[0] through a pointer and keeps s.B.
//
// @Requires s != nil
// @Modifies s.C
// @Ensures s.C'[0] = 1 And s.B' = s.B
func ElementKeepsPlace(s *Shorts) {
	setFirst(&s.C[0], &s.B)
}

// keepsOther writes what p points to and keeps what q points to, which it
// requires to be another value.
//
// @Requires p != nil And q != nil And apart(p, q)
// @Modifies p
// @Ensures *p' = 1 And *q' = *q
func keepsOther(p, q *int16) {
	*p = 1
}

// ApartAtOnePosition hands keepsOther a place and an element at one
// position, which are apart.
//
// @Requires s != nil
// @Modifies s.B
// @Ensures s.C'[0] = s.C[0]
func ApartAtOnePosition(s *Shorts) {
	keepsOther(&s.B, &s.C[0])
}

// LoopKeepsElement writes s.B through a pointer in a loop and keeps s.C[0].
//
// @Requires s != nil And 0 <= n < 100
// @Modifies s.B
// @Ensures s.C'[0] = s.C[0]
func LoopKeepsElement(s *Shorts, n int) {
	p := &s.B
	// @Invariant True
	for range n {
		*p = 2
	}
}
