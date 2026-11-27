package arrayfields

// What one element of an array in a struct covers: the position A + k and
// nothing after it, though it takes n bytes (condition 2 of the ruling on
// the positions of step 3a).

// Bump increments through a pointer.
//
// @Requires p != nil And *p < 1000000
// @Modifies p
// @Ensures *p' = *p + 1
func Bump(p *uint) {
	*p++
}

// ViaPointer bumps one count through a pointer to it, and keeps the
// others and n.
//
// @Requires r != nil And r.c[5] < 1000000
// @Modifies r.c
// @Ensures r.c'[5] = r.c[5] + 1 And r.c'[6] = r.c[6] And r.n' = r.n
func (r *Reader) ViaPointer() {
	Bump(&r.c[5])
}

// Wide holds an array of eight-byte numbers between two fields.
type Wide struct {
	Head int64
	Arr  [4]int64
	Tail int64
}

// zero writes the number a pointer points to.
//
// @Requires p != nil
// @Modifies p
// @Ensures *p' = 0
func zero(p *int64) {
	*p = 0
}

// KeepsNext hands the first element to zero and keeps the second and the
// field after the array.
//
// @Requires w != nil
// @Modifies w.Arr
// @Ensures w.Arr'[0] = 0 And w.Arr'[1] = w.Arr[1] And w.Tail' = w.Tail And w.Head' = w.Head
func KeepsNext(w *Wide) {
	zero(&w.Arr[0])
}

// FirstWithin says that the first element lies within the slice of the
// first one.
//
// @Requires w != nil
// @Ensures True
func FirstWithin(w *Wide) {
	p, s := &w.Arr[0], w.Arr[:1:1]
	// @Assert within(p, s)
	_, _ = p, s
}

// InSlice says that an element of an item's array lies within the slice of
// items.
//
// @Requires |xs| > 2
// @Ensures True
func InSlice(xs []Item) {
	p := &xs[1].Vals[2]
	// @Assert within(p, xs)
	_ = p
}

// FirstHalf zeroes the first half of the array through a slice whose
// capacity ends there, and keeps the second half.
//
// @Requires w != nil
// @Modifies w.Arr
// @Ensures w.Arr'[2] = w.Arr[2] And w.Arr'[3] = w.Arr[3] And w.Arr'[1] = 0
func FirstHalf(w *Wide) {
	s := w.Arr[:2:2]
	// @Invariant Forall k in [0, i) : s[k] = 0
	for i := range s {
		s[i] = 0
	}
}
