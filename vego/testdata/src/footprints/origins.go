package footprints

// Touch writes through s and is handed q beside it.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Touch(s Sink, q *Pair) {
	s.Put(nil)
}

// Box holds a pair and a list of them.
type Box struct {
	P     *Pair
	Items []*Pair
	M     map[int]*Pair
	Out   Sink
	N     int
}

// Maker hands out new pairs.
type Fresh interface {
	// @Ensures p != nil And fresh(p)
	Make() (p *Pair)
}

// FromMap passes a pair read from a map it was given.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func FromMap(s Sink, m map[int]*Pair, k int) {
	Touch(s, m[k])
}

// FromField passes what a field of a parameter holds.
//
// @Requires s != nil And b != nil
// @Modifies s
// @Ensures True
func FromField(s Sink, b *Box) {
	Touch(s, b.P)
}

// EachItem passes every item in a loop.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func EachItem(s Sink, items []*Pair) {
	for k := range items {
		Touch(s, items[k])
	}
}

// Made passes a pair it made.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Made(s Sink) {
	Touch(s, &Pair{A: 1})
}

// FromFresh passes a pair that a contract says is new.
//
// @Requires s != nil And f != nil
// @Modifies s
// @Ensures True
func FromFresh(s Sink, f Fresh) {
	Touch(s, f.Make())
}

// StoresSink stores an interface value and a number into a parameter's
// memory, which pollutes nothing.
//
// @Requires s != nil And b != nil
// @Modifies s, b
// @Ensures True
func StoresSink(s Sink, b *Box) {
	b.Out = s
	b.N = len(b.Items)
	Touch(s, b.P)
}

// FromPeek passes a pair that a call through an interface value returned.
//
// @Requires s != nil And g != nil
// @Modifies s
// @Ensures True
func FromPeek(s Sink, g Peeker) {
	Touch(s, g.Peek()) // want `the footprint of what is passed to Touch as s may hold memory that what is passed as g.Peek\(\) reaches, and Touch relies on it not doing so: it comes from the call of g.Peek at origins.go:\d+:\d+, which is handed g, which is or holds an interface value or a function value, through which it may get memory of any origin`
}

// firstOf returns its first element.
//
// @Requires |ps| > 0
// @Ensures True
func firstOf(ps []*Pair) (p *Pair) {
	return ps[0]
}

// ByTypes passes what a call returned that it handed an unknown slice.
//
// @Requires s != nil And g != nil
// @Modifies s
// @Ensures True
func ByTypes(s Sink, g Peeker) {
	ps := []*Pair{g.Peek()}
	Touch(s, firstOf(ps)) // want `Touch relies on it not doing so: it comes from the call of firstOf at origins.go:\d+:\d+, which is handed ps, and it comes from the call of g.Peek`
}

// StoredNew stores an unknown pair into memory it made, which pollutes it.
//
// @Requires s != nil And g != nil And q != nil
// @Modifies s
// @Ensures True
func StoredNew(s Sink, g Peeker, q *Pair) {
	b := &Box{}
	b.P = g.Peek()
	Touch(s, q) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was stored into memory, and it comes from the call of g.Peek at origins.go:\d+:\d+, which is handed g, which is or holds an interface value or a function value, through which it may get memory of any origin`
}

// InLiteral stores an unknown pair inside a literal called in place.
//
// @Requires s != nil And g != nil And b != nil
// @Modifies s, b
// @Ensures True
func LiteralStores(s Sink, g Peeker, b *Box) {
	func() {
		b.P = g.Peek()
	}()
	Touch(s, b.P) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was`
}

// Deferred touches b at the return, after an unknown pair was stored in b.
//
// @Requires s != nil And g != nil And b != nil
// @Modifies s, b
// @Ensures True
func Deferred(s Sink, g Peeker, b *Box) {
	defer Touch(s, b.P) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was`
	b.P = g.Peek()
}

// LoopStores stores late in a loop body, after the call early in it.
//
// @Requires s != nil And g != nil And b != nil
// @Modifies s, b
// @Ensures True
func LoopStores(s Sink, g Peeker, b *Box) {
	// @Invariant 0 <= i <= 3
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		Touch(s, b.P) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was`
		b.P = g.Peek()
	}
}

// Branches calls before the store on one branch and after it on the other.
//
// @Requires s != nil And g != nil And b != nil
// @Modifies s, b
// @Ensures True
func Branches(s Sink, g Peeker, b *Box, c bool) {
	if c {
		Touch(s, b.P)
		b.P = g.Peek()
	} else {
		b.P = g.Peek()
		Touch(s, b.P) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was stored into memory`
	}
}

// Put stores p into b.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func Put(b *Box, p *Pair) {
	b.P = p
}

// HelperStores hands a helper with targets an unknown pair.
//
// @Requires s != nil And g != nil And b != nil And q != nil
// @Modifies s, b
// @Ensures True
func HelperStores(s Sink, g Peeker, b *Box, q *Pair) {
	Put(b, g.Peek())
	Touch(s, q) // want `Touch relies on it not doing so: the call of Put at origins.go:\d+:\d+ may store a reference into memory it may modify`
}

// Appends appends an unknown pair to a slice of a parameter.
//
// @Requires s != nil And g != nil And b != nil And |b.Items| < 100
// @Modifies s, b, b.Items
// @Ensures True
func Appends(s Sink, g Peeker, b *Box, q *Pair) {
	b.Items = append(b.Items, g.Peek())
	Touch(s, q) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was`
}

// MapStores writes an unknown pair into a map of a parameter.
//
// @Requires s != nil And g != nil And b != nil And b.M != nil
// @Modifies s, b.M
// @Ensures True
func MapStores(s Sink, g Peeker, b *Box, q *Pair) {
	b.M[1] = g.Peek()
	Touch(s, q) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was`
}

// RangeStores stores what it ranges over into a parameter's memory.
//
// @Requires s != nil And b != nil And h != nil
// @Modifies s, b
// @Ensures True
func RangeStores(s Sink, h Shelves, b *Box, q *Pair) {
	for _, p := range h.All() {
		b.P = p
	}
	Touch(s, q) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was`
}

// Shelves hands out a slice of pairs.
type Shelves interface {
	// @Ensures True
	All() (ps []*Pair)
}

// NotOwn passes a writer it got from a field.
//
// @Requires s != nil And b != nil And b.Out != nil And q != nil
// @Modifies s, b.Out
// @Ensures True
func NotOwn(s Sink, b *Box, q *Pair) {
	Touch(b.Out, q) // want `b.Out is not a parameter whose footprint NotOwn's own Modifies lists, so nothing places it`
}

// TouchAll writes through s and is handed qs beside it.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func TouchAll(s Sink, qs []*Pair) {
	s.Put(nil)
}

// Sliced passes a slice of what a call through an interface value returned.
//
// @Requires s != nil And h != nil
// @Modifies s
// @Ensures True
func Sliced(s Sink, h Shelves) {
	ps := h.All()
	TouchAll(s, ps[:0]) // want `TouchAll relies on it not doing so: it comes from the call of h.All`
}

// AppendsInPlace appends an unknown pair to a copy of a parameter's slice,
// which may write into the array it shares with the parameter.
//
// @Requires s != nil And g != nil And b != nil And |b.Items| < 100
// @Modifies s, b.Items
// @Ensures True
func AppendsInPlace(s Sink, g Peeker, b *Box, q *Pair) (n int) {
	local := b.Items
	local = append(local, g.Peek())
	Touch(s, q) // want `Touch relies on it not doing so: at origins.go:\d+:\d+ a value was appended to a slice`
	return len(local)
}
