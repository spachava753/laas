package trialfaults

// A pointer that lies within a struct lies where a field of its type does,
// so a Modifies entry for the struct covers a write through it.

type E struct{ next *E }

type L struct {
	root E
	aux  E
	n    int
}

// W writes through a pointer that lies within l.
//
// @Requires l != nil And p != nil And within(p, l)
// @Modifies l
// @Ensures True
func W(l *L, p *E) {
	p.next = nil
}

// Stale must not keep l.root.next across W, which may write it.
//
// @Requires l != nil
// @Modifies l
// @Ensures True
func Stale(l *L) {
	e := &E{}
	l.root.next = e
	W(l, &l.root)
	// @Assert l.root.next = e // want `assertion may not hold: l.root.next = e`
}

// StaleAux must not keep l.aux.next.
//
// @Requires l != nil
// @Modifies l
// @Ensures True
func StaleAux(l *L) {
	e := &E{}
	l.aux.next = e
	W(l, &l.aux)
	// @Assert l.aux.next = e // want `assertion may not hold: l.aux.next = e`
}

// Narrow lists only the root, while p may be &l.aux.
//
// @Requires l != nil And p != nil And within(p, l)
// @Modifies l.root
// @Ensures True
func Narrow(l *L, p *E) {
	p.next = nil // want `p.next is assigned, which Narrow may not modify: nothing its // @Modifies clauses list is known to cover it`
}

// Other lists l but p lies within m.
//
// @Requires l != nil And m != nil And p != nil And within(p, m)
// @Modifies l
// @Ensures True
func Other(l *L, m *L, p *E) {
	p.next = nil // want `p.next is assigned, which Other may not modify: nothing its // @Modifies clauses list is known to cover it`
}

type M struct{ e E }

type N struct {
	m M
	k int
}

// Deep writes through a pointer two structs down.
//
// @Requires q != nil And p != nil And within(p, q)
// @Modifies q
// @Ensures True
func Deep(q *N, p *E) {
	p.next = nil
}

// @Requires l != nil And p != nil And within(p, l)
// @Modifies l
// @Ensures True
func Self(l *L, p *L) {
	p.n = 1
}

// Keeps: l.n is kept across a write through p to an E.
//
// @Requires l != nil And p != nil And within(p, l) And l.n = 3
// @Modifies l.root, l.aux
// @Ensures l.n' = 3
func Keeps(l *L, p *E) {
	p.next = nil
}

// K holds no E, so no *E lies within one.
type K struct{ n int }

// @Requires p != nil And k != nil And within(p, k) // want `within\(p, k\): no field of K, at any depth, has the type E, so p cannot lie within k`
// @Modifies k
// @Ensures True
func Nowhere(k *K, p *E) {
	p.next = nil
}

// The trial's program: a write through a pointer within the list.
type List struct {
	root E
	n    int
}

// @Requires l != nil And p != nil And within(p, l)
// @Modifies l
// @Ensures True
func Within(l *List, p *E) {
	p.next = nil
}
