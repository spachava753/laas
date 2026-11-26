// Package ownstorage hands a callee memory that an owner it is also handed
// owns, through a type that Go converts to the owned one. The callee
// assumes that nothing it is handed is what the owner owns, so the caller
// must show it, whatever the type of what it hands (a fault at the base of
// F37, found with A5 of its adversarial design review).
package ownstorage

// A is what Holder owns through a pointer.
type A struct{ n int }

// B has the memory of A: Go converts *A to *B.
type B A

// Holder owns the A its field points to.
//
// @Owns p
type Holder struct {
	p *A
}

// MakeHolder makes a Holder whose A is 0.
//
// @Ensures r != nil And r.p != nil And r.p.n = 0
func MakeHolder() (r *Holder) {
	return &Holder{p: &A{}}
}

// use writes b and claims that what h owns is unchanged, which holds when
// b is not part of it.
//
// @Requires h != nil And h.p != nil And b != nil
// @Modifies h, b
// @Ensures h.p' = h.p And h.p.n' = h.p.n
func use(h *Holder, b *B) {
	b.n = 7
	h.p = h.p
}

// Get hands use what h owns, as a *B.
//
// @Requires h != nil And h.p != nil And h.p.n = 0
// @Modifies h
// @Ensures r = 0
func Get(h *Holder) (r int) {
	use(h, (*B)(h.p)) // want `vego: \(\*B\)\(h\.p\) is memory that h owns, and use is handed what reaches a Holder, which can own it; use assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone`
	return h.p.n
}

// GetApart hands use a B of its own.
//
// @Requires h != nil And h.p != nil And h.p.n = 0
// @Modifies h
// @Ensures r = 0
func GetApart(h *Holder) (r int) {
	use(h, &B{})
	return h.p.n
}

// S has the memory of []int: Go converts one to the other.
type S []int

// Pile owns the array of its slice.
//
// @Owns items
type Pile struct {
	items S
}

// MakePile makes a Pile of one 0.
//
// @Ensures r != nil And |r.items| = 1 And r.items[0] = 0
func MakePile() (r *Pile) {
	return &Pile{items: S{0}}
}

// useS writes xs and claims that what p owns is unchanged.
//
// @Requires p != nil And |p.items| > 0 And |xs| > 0
// @Modifies p, xs
// @Ensures p.items' = p.items
func useS(p *Pile, xs []int) {
	xs[0] = 7
	p.items = p.items
}

// GetS hands useS what p owns, as a []int.
//
// @Requires p != nil And |p.items| > 0 And p.items[0] = 0
// @Modifies p
// @Ensures r = 0
func GetS(p *Pile) (r int) {
	useS(p, []int(p.items)) // want `vego: \[\]int\(p\.items\) is memory that p owns, and useS is handed what reaches a Pile, which can own it; useS assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone`
	return p.items[0]
}

// Row owns the array of its slice of A.
//
// @Owns as
type Row struct {
	as []A
}

// MakeRow makes a Row of one A, which is 0.
//
// @Ensures r != nil And |r.as| = 1 And r.as[0].n = 0
func MakeRow() (r *Row) {
	return &Row{as: []A{{}}}
}

// useA writes b and claims that what r owns is unchanged.
//
// @Requires r != nil And |r.as| > 0 And b != nil
// @Modifies r, b
// @Ensures |r.as'| = |r.as| And r.as'[0].n = r.as[0].n
func useA(r *Row, b *B) {
	b.n = 7
	r.as = r.as
}

// GetA hands useA an element of what r owns, as a *B.
//
// @Requires r != nil And |r.as| > 0 And r.as[0].n = 0
// @Modifies r
// @Ensures n = 0
func GetA(r *Row) (n int) {
	useA(r, (*B)(&r.as[0])) // want `vego: \(\*B\)\(&r\.as\[0\]\) is memory that r owns, and useA is handed what reaches a Row, which can own it; useA assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone`
	return r.as[0].n
}

// nest is trusted: its result holds xs.
func nest(xs []int) [][]int { return [][]int{xs} }

// Nest hands nest what p owns; nest's result may hold it below its top
// level as a []int, which Go converts S to.
//
// @Requires p != nil And |p.items| > 0
// @Ensures True
func Nest(p *Pile) (n int) {
	r := nest(p.items) // want `vego: what is handed to nest as xs is memory that p owns, and what nest returns may hold parts of it that its entry does not place; copy the memory first, as with bytes\.Clone or slices\.Clone`
	return len(r)
}
