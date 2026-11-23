package owns

import "strings"

// Converting an owner of the project to an interface whose methods write
// behind their receiver (F27, step 4): the row of the value holds the
// struct and what it owns at the conversion, and follows what is stored
// into its owned fields after.

// Store is an interface of the project whose Put writes behind its
// receiver.
type Store interface {
	// @Receiver r
	// @Modifies r
	// @Ensures True
	Put(k string, v int)
}

// memStore owns its map.
//
// @Owns m
type memStore struct {
	m map[string]int
}

// Put stores v under k, making the map when it is nil.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *memStore) Put(k string, v int) {
	if s.m == nil {
		s.m = make(map[string]int)
	}
	s.m[k] = v
}

// Regrow gives the store a new map, called directly.
//
// @Requires s != nil
// @Modifies s
// @Ensures s.m' != nil
func (s *memStore) Regrow() {
	s.m = make(map[string]int)
}

// PutThrough converts a store and puts through it twice.
//
// @Ensures True
func PutThrough() {
	s := &memStore{}
	var i Store = s
	i.Put("a", 1)
	i.Put("b", 2)
}

// StaleAfterStore keeps a fact about a map stored into the converted
// store after the conversion, across a Put through it, which writes that
// map (the part 1 reviewer's program).
//
// @Ensures r
func StaleAfterStore() (r bool) {
	s := &memStore{m: map[string]int{}}
	var i Store = s
	s.m = make(map[string]int)
	m := s.m
	m["a"] = 1
	i.Put("a", 2)
	return m["a"] == 1 // want `vego: postcondition may not hold: r`
}

// StaleAfterCall does it with a map a direct call made.
//
// @Ensures r
func StaleAfterCall() (r bool) {
	s := &memStore{m: map[string]int{}}
	var i Store = s
	s.Regrow()
	m := s.m
	m["a"] = 1
	i.Put("a", 2)
	return m["a"] == 1 // want `vego: postcondition may not hold: r`
}

// KeptBeside keeps a map it made that the store does not own across a Put.
//
// @Ensures r
func KeptBeside() (r bool) {
	s := &memStore{}
	var i Store = s
	other := map[string]int{"a": 1}
	i.Put("a", 2)
	return other["a"] == 1
}

// StaleInLoop stores a new map in a loop after the conversion (F3 of the
// design review).
//
// @Ensures r
func StaleInLoop() (r bool) {
	s := &memStore{m: map[string]int{}}
	var i Store = s
	// @Invariant 0 <= j <= 1 And s.m != nil
	// @Variant 1 - j
	for j := 0; j < 1; j++ {
		s.m = make(map[string]int)
	}
	m := s.m
	m["a"] = 1
	i.Put("a", 2)
	return m["a"] == 1 // want `vego: postcondition may not hold: r`
}

// StaleInBranch stores a new map on each branch, whose layers the join
// keeps (F3).
//
// @Ensures r
func StaleInBranch(c bool) (r bool) {
	s := &memStore{m: map[string]int{}}
	var i Store = s
	if c {
		s.m = make(map[string]int)
	} else {
		s.m = map[string]int{}
	}
	m := s.m
	m["a"] = 1
	i.Put("a", 2)
	return m["a"] == 1 // want `vego: postcondition may not hold: r`
}

// Adder is an interface whose method writes behind its receiver.
type Adder interface {
	// @Receiver a
	// @Modifies a
	// @Ensures True
	Add()
}

// Page holds a Builder by value, so it owns what the Builder owns.
type Page struct {
	sb strings.Builder
}

// Add writes a byte while the Builder is short, called through the value
// and directly.
//
// @Requires d != nil
// @Modifies d
// @Ensures True
func (d *Page) Add() {
	if d.sb.Len() < 1000 {
		d.sb.WriteByte('x')
	}
}

// GrowBetween converts a Page and grows its Builder by a direct call between
// calls through the value; a slice made after the growth is kept.
//
// @Ensures r
func GrowBetween() (r bool) {
	d := &Page{}
	var i Adder = d
	i.Add()
	d.Add()
	buf := make([]byte, 1)
	buf[0] = 1
	i.Add()
	return buf[0] == 1
}

// Tally owns its counts.
//
// @Owns items
type Tally struct {
	items []int
	total int
}

// Record writes the first count.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func (t *Tally) Add() {
	if len(t.items) > 0 && t.items[0] < 1000 {
		t.items[0]++
	}
}

// useTally writes through a and keeps xs.
//
// @Requires a != nil And |xs| = 1
// @Modifies a
// @Ensures xs'[0] = xs[0]
func useTally(a Adder, xs []int) {
	a.Add()
}

// TallyBeside hands a converted Tally beside what it owns (F4 of the design
// review).
//
// @Ensures True
func TallyBeside() {
	t := &Tally{items: []int{5}}
	useTally(t, t.items) // want `vego: t.items is memory that the Tally made at convert.go:[0-9:]+ owns`
}

// OwnsItself owns an Adder, and is one.
//
// @Owns out
type OwnsItself struct {
	out Adder
	n   int
}

// Add counts.
//
// @Requires o != nil
// @Modifies o
// @Ensures True
func (o *OwnsItself) Add() {
	if o.n < 1000 {
		o.n++
	}
}

// IntoItself converts an owner into its own owned field, so that its row
// would be its own struct (the reviewer's program of step 4).
//
// @Ensures True
func IntoItself() {
	r := &OwnsItself{}
	r.out = r // want `vego: r.out may come to hold r itself, whose footprint would then lie in what it owns; an owner cannot own itself`
}

// StaleAtConversion keeps a fact about the map the store owned at the
// conversion across a Put through it.
//
// @Ensures r
func StaleAtConversion() (r bool) {
	s := &memStore{m: map[string]int{"a": 1}}
	var i Store = s
	i.Put("a", 2)
	return s.m["a"] == 1 // want `vego: postcondition may not hold: r`
}

// CacheThrough converts a Cache, which makes its map when it is nil, to a
// Store and puts through it.
//
// @Ensures True
func CacheThrough() {
	c := &Cache{}
	var i Store = c
	i.Put("a", 1)
	i.Put("b", 2)
}
