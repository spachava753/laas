// Package errorsvarsclient reads the aliases and opaque error variables of
// another package, from what that package published.
package errorsvarsclient

import "errorsvars"

// Aliases compares aliases of another package with what they hold.
//
// @Ensures same
func Aliases() (same bool) {
	return errorsvars.ErrAlias == errorsvars.ErrMine && errorsvars.ErrMissing == errorsvars.ErrMine && errorsvars.ErrChain == errorsvars.ErrMine
}

// Code compares an unknown error with an opaque variable of another
// package whose type makes == identity, which is not nil.
//
// @Ensures r
func Code(e error) (same, r bool) {
	return e == errorsvars.ErrCode, errorsvars.ErrCode != nil
}

// Named cannot show that an opaque variable whose type is not known is
// not nil.
//
// @Ensures r
func Named() (r bool) {
	return errorsvars.ErrNamed != nil // want `vego: postcondition may not hold: r`
}

// SameSlice compares an unknown error with one whose type is a slice.
//
// @Ensures True
func SameSlice(e error) (same bool) {
	return e == errorsvars.ErrSlice // want `vego: cannot verify SameSlice: comparing two errors can panic when both hold the same uncomparable type`
}
