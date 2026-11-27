package arrayptrs

// NilIndex indexes a nil pointer to an array, which panics.
//
// @Ensures True
func NilIndex() (r int) {
	var p *[4]int
	return p[1] // want `vego: pointer may be nil`
}

// NilDeref reads what a nil pointer to an array points to.
//
// @Ensures True
func NilDeref() (r [4]int) {
	var p *[4]int
	return *p // want `vego: pointer may be nil`
}

// NilRangeValues ranges over the values of a nil pointer to an array.
//
// @Ensures True
func NilRangeValues() (r int) {
	var p *[4]int
	// @Invariant True
	for _, x := range p { // want `vego: pointer may be nil`
		r = x
	}
	return r
}

// Short converts a slice that may be too short.
//
// @Requires |xs| >= 2
// @Ensures True
func Short(xs []int) {
	_ = (*[4]int)(xs) // want `vego: the conversion may panic`
}

// Unlisted writes through a pointer to an array of a struct it does not
// list.
//
// @Requires b != nil
// @Ensures True
func Unlisted(b *Block) {
	p := &b.Word
	p[0] = 1 // want `p\[0\] is assigned, which Unlisted may not modify`
}

// Wrong claims that a write through a pointer kept the element.
//
// @Requires b != nil And b.Word[2] = 1
// @Modifies b.Word
// @Ensures b.Word'[2] = 1
func Wrong(b *Block) {
	p := &b.Word
	p[2] = 7
} // want `vego: postcondition may not hold: b\.Word'\[2\] = 1`

// Param takes a pointer to an array.
//
// @Requires p != nil
// @Ensures True
func Param(p *[4]int) { // want `cannot verify Param: parameter p has type \*\[4\]int, a pointer to an array, and pointers to arrays are supported only in local variables yet`
}

// Result returns one.
//
// @Ensures True
func Result() (r *[4]int) { // want `cannot verify Result: result r has type \*\[4\]int, a pointer to an array`
	return new([4]int)
}

// Holder holds one in a field.
type Holder struct {
	P *[4]int
}

// Field stores one in a field.
//
// @Requires h != nil
// @Modifies h
// @Ensures True
func Field(h *Holder) {
	h.P = new([4]int) // want `field P has unsupported type \*\[4\]int`
}

// Captured is captured by a function literal.
//
// @Ensures True
func Captured() {
	p := new([4]int)
	f := func() { p[0] = 1 } // want `p, which a function literal captures, has type \*\[4\]int, a pointer to an array`
	f()
}

// Into converts one to an interface value.
//
// @Ensures True
func Into() (r any) {
	return new([4]int) // want `the value converted to any has type \*\[4\]int, a pointer to an array`
}

// NilRangeWrite writes through a nil pointer to an array in a range over
// its indices: Go runs the loop four times, and the first write panics.
//
// @Ensures True
func NilRangeWrite() {
	var p *[4]int
	// @Invariant True
	for i := range p {
		p[i] = 1 // want `vego: pointer may be nil`
	}
}

// Stack owns its items.
//
// @Owns items
type Stack struct {
	items []int
}

// Clear zeroes the first item.
//
// @Requires s != nil And |s.items| > 0
// @Modifies s
// @Ensures s.items'[0] = 0 And |s.items'| = |s.items|
func (s *Stack) Clear() {
	s.items[0] = 0
}

// Stale reads the first item through a pointer to the items' array after
// a method changed it, and claims the old value.
//
// @Requires s != nil And |s.items| >= 2 And s.items[0] = 5
// @Modifies s
// @Ensures r = 5
func (s *Stack) Stale() (r int) {
	p := (*[2]int)(s.items)
	s.Clear()
	return p[0] // want `vego: postcondition may not hold: r = 5`
}
