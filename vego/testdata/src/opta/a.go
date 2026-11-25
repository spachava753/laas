// Package opta gives optlibx.Sizer an entry, so it checks conversions to
// optlib.W against Sizer, and relies on that check (D5 of F35).
package opta

import (
	"optlib"
	"optlibx"
)

// Sized writes and has a size.
type Sized struct{}

// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil) And err = nil
func (Sized) Write(p []byte) (n int, err error) { return len(p), nil }

// @Ensures n = 1
func (Sized) Size() (n int) { return 1 }

// @Ensures w != nil
func Make() (w optlib.W) {
	return Sized{}
}

// SizeOf finds the size of a writer it is handed.
//
// @Requires w != nil
// @Ensures n >= 0
func SizeOf(w optlib.W) (n int) {
	if s, ok := w.(optlibx.Sizer); ok {
		return s.Size()
	}
	return 0
}
