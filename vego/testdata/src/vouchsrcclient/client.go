// Package vouchsrcclient makes and calls values of types whose contracts,
// in another package, vouch for their errors.
package vouchsrcclient

import (
	"errors"
	"fmt"

	"vouchsrc"
)

// Wraps wraps the error of a Store of another package.
//
// @Requires s != nil
// @Ensures True
func Wraps(s vouchsrc.Store) (err error) {
	_, err = s.Read()
	if err != nil {
		return fmt.Errorf("client: %w", err)
	}
	return nil
}

// own is a Store of this package.
type own struct{ n int }

// @Ensures err = nil <-> o.n != 0
func (o own) Read() (data []byte, err error) {
	if o.n == 0 {
		return nil, errors.New("none")
	}
	return nil, nil
}

// @Ensures err = nil
func (own) Write(data []byte) (err error) {
	return nil
}

// @Ensures s != nil
func Make() (s vouchsrc.Store) {
	return own{}
}

// relay hands on an error it was given.
type relay struct{ err error }

// @Ensures err = r.err
func (r relay) Read() (data []byte, err error) {
	return nil, r.err
}

// @Ensures err = nil
func (relay) Write(data []byte) (err error) {
	return nil
}

// @Ensures s != nil
func MakeRelay(e error) (s vouchsrc.Store) {
	return relay{err: e} // want `Read may return an error whose origin is not known in err, and the contract of Store.Read vouches for the errors there`
}
