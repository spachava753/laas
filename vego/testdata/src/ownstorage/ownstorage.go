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

// Point lies inside an Item, at an offset that is not 0.
type Point struct{ x int }

// Item holds a Point and an array.
type Item struct {
	prefix int
	point  Point
	buf    [4]byte
}

// Items owns the array of its slice of Item.
//
// @Owns items
type Items struct {
	items []Item
}

// MakeItems makes Items of one zero Item.
//
// @Ensures r != nil And |r.items| = 1
func MakeItems() (r *Items) {
	return &Items{items: []Item{{}}}
}

// writePoint writes p and claims that the Point of the first owned Item is
// unchanged.
//
// @Requires r != nil And |r.items| > 0 And p != nil
// @Modifies r, p
// @Ensures |r.items'| = |r.items| And r.items'[0].point.x = r.items[0].point.x
func writePoint(r *Items, p *Point) {
	p.x = 7
	r.items = r.items
}

// SetInside hands writePoint a pointer inside an owned element (A9 of the
// adversarial review of F37).
//
// @Requires r != nil And |r.items| > 0
// @Modifies r
// @Ensures True
func SetInside(r *Items) {
	writePoint(r, &r.items[0].point) // want `vego: &r\.items\[0\]\.point is memory that r owns, and writePoint is handed what reaches a Items, which can own it; writePoint assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone`
}

// writeBytes writes b and claims that the array of the first owned Item is
// unchanged, which it cannot show: a callee assumes no slice of another
// element type apart from what an owner owns, so a caller may hand it a
// slice of an array inside an owned element.
//
// @Requires r != nil And |r.items| > 0 And |b| > 0
// @Modifies r, b
// @Ensures |r.items'| = |r.items| And r.items'[0].buf[0] = r.items[0].buf[0]
func writeBytes(r *Items, b []byte) {
	b[0] = 7
	r.items = r.items
} // want `vego: postcondition may not hold: r\.items'\[0\]\.buf\[0\] = r\.items\[0\]\.buf\[0\]`

// Outer holds a Point inside it.
type Outer struct {
	n  int
	in Point
}

// Boxed owns the Outer its field points to.
//
// @Owns p
type Boxed struct {
	p *Outer
}

// MakeBoxed makes a Boxed whose Point is 0.
//
// @Ensures r != nil And r.p != nil And r.p.in.x = 0
func MakeBoxed() (r *Boxed) {
	return &Boxed{p: &Outer{}}
}

// writeIn writes q and claims that the owned Outer's Point is unchanged,
// which it cannot show: a callee assumes apart from an owned struct only a
// pointer to a struct of its type, so a caller may hand it a pointer
// inside the owned struct.
//
// @Requires b != nil And b.p != nil And q != nil
// @Modifies b, q
// @Ensures b.p' = b.p And b.p.in.x' = b.p.in.x
func writeIn(b *Boxed, q *Point) {
	q.x = 7
	b.p = b.p
} // want `vego: postcondition may not hold: b\.p\.in\.x' = b\.p\.in\.x`

// project is trusted: what it returns points into the first element of
// what it is handed.
func project(xs []Item) []*Point { return []*Point{&xs[0].point} }

// Pick hands project what r owns (A10).
//
// @Requires r != nil And |r.items| > 0
// @Ensures True
func Pick(r *Items) (n int) {
	got := project(r.items) // want `vego: what is handed to project as xs is memory that r owns, and what project returns may hold parts of it that its entry does not place; copy the memory first, as with bytes\.Clone or slices\.Clone`
	return len(got)
}

// List holds lists.
type List []List

// Lists owns its list.
//
// @Owns l
type Lists struct {
	l List
}

// wrap is trusted: what it returns holds what it is handed.
func wrap(l List) List { return List{l} }

// Nested hands wrap what h owns, which the result holds below its top
// level, in a type that holds itself (A11).
//
// @Requires h != nil
// @Ensures True
func Nested(h *Lists) (n int) {
	r := wrap(h.l) // want `vego: what is handed to wrap as l is memory that h owns, and what wrap returns may hold parts of it that its entry does not place; copy the memory first, as with bytes\.Clone or slices\.Clone`
	return len(r)
}

// M has the memory of map[string]int: Go converts one to the other.
type M map[string]int

// Table owns its map.
//
// @Owns m
type Table struct {
	m M
}

// useM writes x. A callee assumes no map of another type apart from what
// an owner owns, so it cannot claim that the owned map is unchanged.
//
// @Requires t != nil And t.m != nil And x != nil
// @Modifies t, x
// @Ensures t.m' = t.m
func useM(t *Table, x map[string]int) {
	x["a"] = 7
	t.m = t.m
}

// GetM hands useM what t owns, as a map[string]int. The callee assumes
// nothing of it, but the call is refused, as one of a slice of a named type
// is (F17 of the review of the storage fix).
//
// @Requires t != nil And t.m != nil
// @Modifies t
// @Ensures True
func GetM(t *Table) {
	useM(t, map[string]int(t.m)) // want `vego: map\[string\]int\(t\.m\) is memory that t owns, and useM is handed what reaches a Table, which can own it; useM assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone`
}
