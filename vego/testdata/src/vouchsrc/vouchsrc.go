// Package vouchsrc declares an interface and a function type whose
// contracts vouch for the errors they return.
package vouchsrc

import (
	"errors"
	"fmt"
)

// Store keeps data.
type Store interface {
	// @Ensures True
	// @Vouches err
	Read() (data []byte, err error)
	// @Ensures True
	Write(data []byte) (err error)
}

// Load reads a store and wraps its error.
//
// @Requires s != nil
// @Ensures True
func Load(s Store) (n int, err error) {
	data, err := s.Read()
	if err != nil {
		return 0, fmt.Errorf("read: %w", err)
	}
	return len(data), nil
}

// Save cannot wrap the error of Write, which nothing vouches for.
//
// @Requires s != nil
// @Ensures True
func Save(s Store) (err error) {
	err = s.Write(nil)
	if err != nil {
		return fmt.Errorf("write: %w", err) // want `cannot verify Save: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// Fetch is a function type whose values vouch for their errors.
//
// @Ensures True
// @Vouches err
type Fetch func() (n int, err error)

// Run calls a Fetch and wraps its error.
//
// @Requires f != nil
// @Ensures True
func Run(f Fetch) (err error) {
	_, err = f()
	if err != nil {
		return fmt.Errorf("fetch: %w", err)
	}
	return nil
}

// memory is a Store that returns errors it made.
type memory struct{ data []byte }

// @Ensures err = nil <-> m.data != nil
func (m memory) Read() (data []byte, err error) {
	if m.data == nil {
		return nil, errors.New("empty")
	}
	return m.data, nil
}

// @Ensures err = nil
func (m memory) Write(data []byte) (err error) {
	return nil
}

// @Ensures s != nil
func NewMemory() (s Store) {
	return memory{}
}

// stale is a Store that returns an error it was given, of unknown origin.
type stale struct{ err error }

// @Ensures err = s.err
func (s stale) Read() (data []byte, err error) {
	return nil, s.err
}

// @Ensures err = nil
func (s stale) Write(data []byte) (err error) {
	return nil
}

// @Ensures s != nil
func NewStale(e error) (s Store) {
	return stale{err: e} // want `Read may return an error whose origin is not known in err, and the contract of Store.Read vouches for the errors there`
}

// @Ensures f != nil
func MakeFetch() (f Fetch) {
	return func() (n int, err error) {
		return 1, errors.New("no")
	}
}

// @Ensures f != nil
func MakeFetchWrong(e error) (f Fetch) {
	return func() (n int, err error) { // want `the function literal may return an error whose origin is not known in err, and the contract of Fetch vouches for the errors there`
		return 1, e
	}
}
