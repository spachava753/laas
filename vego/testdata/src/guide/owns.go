package guide

import (
	"guidestore"
	"io"
	"os"
)

// The programs of "Structs that own memory" in the guide (F27).

// Pile owns the array of its slice.
//
// @Owns items
type Pile struct {
	items []int
}

// Push appends x.
//
// @Requires p != nil And |p.items| < 1000000
// @Modifies p
// @Ensures |p.items'| = |p.items| + 1 And p.items'[|p.items|] = x
func (p *Pile) Push(x int) {
	p.items = append(p.items, x)
}

// PushTwice pushes twice onto a pile it is handed.
//
// @Requires p != nil And |p.items| < 1000
// @Modifies p
// @Ensures |p.items'| = |p.items| + 2
func PushTwice(p *Pile) {
	p.Push(1)
	p.Push(2)
}

// NewPile makes a pile and pushes onto it, with no Modifies.
//
// @Ensures r != nil And |r.items| = 2
func NewPile() (r *Pile) {
	r = &Pile{}
	r.Push(1)
	r.Push(2)
	return r
}

// Take makes a pile own a slice it is handed.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func Take(p *Pile, xs []int) {
	p.items = xs // want `vego: p.items may come to refer to memory that existed when Take was called and that it did not own; an owned field may refer only to memory made since, or to part of what it referred to then; copy it into new memory, as slices.Clone does, or do not declare the field owned`
}

// Shelf holds a slice it does not own.
type Shelf struct {
	kept []int
}

// Lend keeps what a pile owns in another struct.
//
// @Requires p != nil And s != nil
// @Modifies s
// @Ensures True
func Lend(p *Pile, s *Shelf) {
	s.kept = p.items // want `vego: p.items is memory that p owns, stored into memory at owns.go:[0-9:]+; it may be read and written here, but not kept elsewhere: copy it, or do not declare the field owned`
}

// Items returns what the pile owns, as its contract says.
//
// @Requires p != nil
// @Ensures within(r, p) And |r| = |p.items|
func (p *Pile) Items() (r []int) {
	return p.items
}

// Append pushes what xs holds; xs is not what p owns, so it stays as it
// was while p grows.
//
// @Requires p != nil And |p.items| + |xs| < 1000000
// @Modifies p
// @Ensures |p.items'| = |p.items| + |xs|
func (p *Pile) Append(xs []int) {
	// @Invariant 0 <= i <= |xs| And |p.items| = |old(p.items)| + i
	for i := range xs {
		p.items = append(p.items, xs[i])
	}
}

// AppendOwn hands a pile what it owns.
//
// @Requires p != nil And |p.items| < 1000
// @Modifies p
// @Ensures True
func AppendOwn(p *Pile) {
	p.Append(p.items) // want `vego: p.items is memory that p owns, and Append is handed what reaches a Pile, which can own it; Append assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone`
}

// Journal owns the writer it writes to.
//
// @Owns out
type Journal struct {
	out   io.Writer
	lines int
}

// NewJournal makes a journal over standard error.
//
// @Ensures r != nil And r.out != nil And r.lines = 0 And fresh(r)
func NewJournal() (r *Journal) {
	return &Journal{out: os.Stderr}
}

// Line writes p and counts it: the count is kept across the write.
//
// @Requires l != nil And l.out != nil And l.lines < 1000000
// @Modifies l
// @Ensures err = nil -> l.lines' = l.lines + 1
func (l *Journal) Line(p []byte) (err error) {
	_, err = l.out.Write(p)
	if err == nil {
		l.lines++
	}
	return err
}

// Jot writes a line to a journal it makes.
//
// @Ensures True
func Jot(p []byte) {
	l := NewJournal()
	_ = l.Line(p)
}

// Putter is an interface whose method writes behind its receiver.
type Putter interface {
	// @Receiver r
	// @Modifies r
	// @Ensures True
	Put(k string, v int)
}

// Registry owns its map.
//
// @Owns m
type Registry struct {
	m map[string]int
}

// Put stores v under k, making the map when it is nil.
//
// @Requires x != nil
// @Modifies x
// @Ensures True
func (x *Registry) Put(k string, v int) {
	if x.m == nil {
		x.m = make(map[string]int)
	}
	x.m[k] = v
}

// PutTwice converts an index and puts through it twice.
//
// @Ensures True
func PutTwice() {
	x := &Registry{}
	var p Putter = x
	p.Put("a", 1)
	p.Put("b", 2)
}

// StaleRegistry keeps a fact about a map stored after the conversion.
//
// @Ensures r
func StaleRegistry() (r bool) {
	x := &Registry{m: map[string]int{}}
	var p Putter = x
	x.m = make(map[string]int)
	m := x.m
	m["a"] = 1
	p.Put("a", 2)
	return m["a"] == 1 // want `vego: postcondition may not hold: r`
}

// Service owns a store of another package, so its invariant includes the
// store's, though the store's fields cannot be named here.
//
// @Owns store
// @Invariant store != nil
type Service struct {
	store *guidestore.Store
}

// Rename sets a name in the store the service owns.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Service) Rename(id int, name string) {
	s.store.Set(id, name)
}

// RenameAll sets names in a loop, which keeps the store's invariant with
// valid(s).
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Service) RenameAll(names []string) {
	// @Invariant valid(s)
	for i := range names {
		s.store.Set(i, names[i])
	}
}

// RenameAllForgets is RenameAll without the invariant.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Service) RenameAllForgets(names []string) {
	// @Invariant s.store != nil
	for i := range names {
		s.store.Set(i, names[i]) // want `vego: invariant of Store may not hold for what is passed to Set as st: names != nil`
	}
} // want `vego: invariant of Store may not hold for s on return, in what it owns at store: names != nil`
