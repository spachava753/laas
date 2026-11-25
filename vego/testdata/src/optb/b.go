// Package optb has no trust file, so it does not count optlibx.Sizer, and
// its conversions to optlib.W are not checked against it.
package optb

import "optlib"

// Negative writes and has a size below zero.
type Negative struct{}

// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (Negative) Write(p []byte) (n int, err error) { return len(p), nil }

// Size is not checked by this module.
func (Negative) Size() int { return -1 }

// @Ensures w != nil
func Make() (w optlib.W) {
	return Negative{}
}

// S2 is an io.Writer of package optb, whose build holds optlibx through
// optlib.
type S2 interface{ optlib.W }

// @Ensures s != nil
func Make2() (s S2) {
	return Negative{}
}
