// Package guidestore is the store of another package in the guide's
// example of the invariant of what a struct owns (F27).
package guidestore

// Store keeps names under ids, in a map that is never nil.
//
// @Owns names
// @Invariant names != nil
type Store struct {
	names map[int]string
}

// New makes an empty store.
//
// @Ensures r != nil And fresh(r)
func New() (r *Store) {
	return &Store{names: make(map[int]string)}
}

// Set stores a name; it needs the invariant, since a nil map panics.
//
// @Requires st != nil
// @Modifies st
// @Ensures True
func (st *Store) Set(id int, name string) {
	st.names[id] = name
}
