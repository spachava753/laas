// Package rewindsnone relies on an entry of Rewinder that says Rewind does
// not rewind.
package rewindsnone

import "rewindlib"

// Back calls Rewind.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Back(s rewindlib.Rewinder) {
	s.Rewind()
}
