// Package ownsptr holds pointers to single values that lie in memory an
// owner owns (F3 of the design review of F42).
package ownsptr

// Stack owns its items.
//
// @Owns items
type Stack struct {
	items []int
	n     int
}

// Set writes the first item and then what p points to, relying on C3: p
// lies outside what s owns.
//
// @Requires s != nil And p != nil And |s.items| > 0
// @Modifies s, p
// @Ensures s.items'[0] = 1
func (s *Stack) Set(p *int) {
	s.items[0] = 1
	*p = 2
}

// SetOwn hands Set a pointer into what s owns.
//
// @Requires s != nil And |s.items| > 0
// @Modifies s
// @Ensures True
func SetOwn(s *Stack) {
	s.Set(&s.items[0]) // want `vego: &s\.items\[0\] is memory that s owns, and Set is handed what reaches a Stack, which can own it`
}

// Top returns a pointer into what s owns, and says so.
//
// @Requires s != nil And |s.items| > 0
// @Ensures within(r, s)
func (s *Stack) Top() (r *int) {
	return &s.items[0]
}

// TopUnsaid returns a pointer into what s owns without saying so.
//
// @Requires s != nil And |s.items| > 0
// @Ensures True
func (s *Stack) TopUnsaid() (r *int) {
	return &s.items[0] // want `vego: TopUnsaid returns memory that s owns; say so with within\(r, s\) in an Ensures, or return a copy`
}

// Holder keeps a pointer.
type Holder struct {
	p *int
}

// Keep stores a pointer into what s owns into memory.
//
// @Requires s != nil And h != nil And |s.items| > 0
// @Modifies h
// @Ensures True
func Keep(s *Stack, h *Holder) {
	h.p = &s.items[0] // want `vego: &s\.items\[0\] is memory that s owns, stored into memory`
}

// Inner is what an Outer owns through a pointer.
type Inner struct {
	n int
}

// Outer owns the Inner its field points to.
//
// @Owns in
type Outer struct {
	in *Inner
}

// SetIn writes the inner number and then what p points to.
//
// @Requires o != nil And o.in != nil And p != nil
// @Modifies o, p
// @Ensures o.in.n' = 1
func (o *Outer) SetIn(p *int) {
	o.in.n = 1
	*p = 2
}

// SetInOwn hands SetIn a pointer into what o owns.
//
// @Requires o != nil And o.in != nil
// @Modifies o
// @Ensures True
func SetInOwn(o *Outer) {
	o.SetIn(&o.in.n) // want `vego: &o\.in\.n is memory that o owns, and SetIn is handed what reaches a Outer, which can own it`
}
