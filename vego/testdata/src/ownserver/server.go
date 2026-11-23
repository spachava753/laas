// Package ownserver holds a store of another package through an owned
// pointer field, as the trial's task server does: its handlers name no
// field of the store (F27, step 2).
package ownserver

import "ownstore"

// Server owns the store its field points to, so its invariant includes
// the store's.
//
// @Owns store
// @Invariant store != nil
type Server struct {
	store *ownstore.Store
}

// New makes a server with a new store.
//
// @Ensures result != nil And ~held(result.store.Mutex)
func New() (result *Server) {
	return &Server{store: ownstore.New()}
}

// Clear clears the store, under Modifies s, with the store's invariant
// known from the server's.
//
// @Requires s != nil And ~held(s.store.Mutex)
// @Modifies s
// @Ensures ~held(s.store'.Mutex')
func (s *Server) Clear() {
	s.store.Clear()
}

// Count creates a task for each text, in a loop: the loop forgets the
// store, and valid(s) brings its invariant back at the head.
//
// @Requires s != nil And ~held(s.store.Mutex)
// @Modifies s
// @Ensures ~held(s.store'.Mutex')
func (s *Server) Count(texts []string) {
	// @Invariant valid(s) And ~held(s.store.Mutex)
	for i := range texts {
		s.store.Create(texts[i])
	}
}

// CountForgets is Count without valid(s) at the loop's head.
//
// @Requires s != nil And ~held(s.store.Mutex)
// @Modifies s
// @Ensures ~held(s.store'.Mutex')
func (s *Server) CountForgets(texts []string) {
	// @Invariant s.store != nil And ~held(s.store.Mutex)
	for i := range texts {
		s.store.Create(texts[i]) // want `vego: invariant of Store may not hold for what is passed to Create as st: tasks != nil` `vego: invariant of Store may not hold for what is passed to Create as st: 0 <= nextID`
	}
} // want `vego: invariant of Store may not hold for s on return, in what it owns at store: tasks != nil` `vego: invariant of Store may not hold for s on return, in what it owns at store: 0 <= nextID`

// Repair hands the store to a helper of its package that is handed it
// under valid, and proves its own invariant from what the helper ensures.
//
// @Requires s != nil And valid(s)
// @Modifies s
// @Ensures valid(s')
func (s *Server) Repair() {
	ownstore.Reset(s.store)
}

// Plain holds a store through a pointer it does not own. It has a field
// more than Server: a struct type identical to Server would own what
// Server owns, since a declaration is matched by the underlying struct.
//
// @Invariant store != nil
type Plain struct {
	store *ownstore.Store
	name  string
}

// Clear is Server.Clear without ownership: the store's invariant is not
// known.
//
// @Requires p != nil And ~held(p.store.Mutex)
// @Modifies p.store
// @Ensures True
func (p *Plain) Clear() {
	p.store.Clear() // want `vego: invariant of Store may not hold for what is passed to Clear as st: tasks != nil` `vego: invariant of Store may not hold for what is passed to Clear as st: 0 <= nextID`
}

// NoInvariant asks valid of a type that has none.
//
// @Requires b != nil And valid(b) // want `valid needs a struct type with an invariant, and Box has none, neither its own nor through what it owns`
// @Ensures True
func NoInvariant(b *Box) {}

// Box has no invariant.
type Box struct {
	n int
}

// In names valid in the invariant of a type, which is refused.
//
// @Invariant valid(inner) // want `valid\(inner\) cannot stand in the invariant of a type`
type In struct {
	inner *Server
}

// Result names a result valid, which stays a name.
//
// @Requires s != nil
// @Ensures valid <-> s.store != nil
func Result(s *Server) (valid bool) {
	return s.store != nil
}

// Primed says valid of the store on return through a primed path.
//
// @Requires s != nil And valid(s) And ~held(s.store.Mutex)
// @Modifies s
// @Ensures valid(s.store')
func (s *Server) Primed() {
	s.store.Clear()
}

// BrokenUse asks valid of a type whose invariant could not be read.
//
// @Requires x != nil And valid(x) // want `valid\(x\): the invariants of In cannot be used: an Invariant annotation of In could not be read`
// @Ensures True
func BrokenUse(x *In) {} // want `vego: the invariants of In cannot be used: an Invariant annotation of In could not be read, or they contradict each other, as reported at them, so they are neither assumed nor proved here`

func external(s *Server) {}

// CallsExternal calls a trusted function whose entry names valid.
//
// @Requires s != nil
// @Ensures True
func CallsExternal(s *Server) {
	external(s) // want `vego: the trusted contract of ownserver.external \(trusted.yaml:[0-9]+\) cannot be used: in its requires "valid\(s\)": valid\(s\) cannot stand in a trusted contract; state the clauses it stands for`
}

// Replace gives the server a store whose map is nil, which breaks the
// invariant of what the server owns.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Server) Replace() {
	s.store = &ownstore.Store{}
} // want `vego: invariant of Store may not hold for s on return, in what it owns at store: tasks != nil`

// ReplaceInLoop does it in a loop that claims valid(s).
//
// @Requires s != nil And 0 <= n
// @Modifies s
// @Ensures True
func (s *Server) ReplaceInLoop(n int) {
	// @Invariant valid(s) And 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ { // want `vego: loop invariant may not be preserved: valid\(s\)`
		s.store = &ownstore.Store{}
	}
}

// Lazy owns a store it may drop: the invariant of the store is asked only
// of a store that is there (F23 of the review of step 2).
//
// @Owns st
type Lazy struct {
	st *ownstore.Store
}

// Drop drops the store.
//
// @Requires l != nil
// @Modifies l
// @Ensures True
func (l *Lazy) Drop() {
	l.st = nil
}

// Swapped asserts in a body what a boundary assumed of s on entry, with
// valid(old(s)), after it gave s a new store (F24 of the review of step 2).
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s *Server) Swapped() {
	s.store = ownstore.New()
	// @Assert valid(old(s)) And valid(s)
}
