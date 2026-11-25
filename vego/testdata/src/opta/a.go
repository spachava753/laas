// Package opta gives optlibx.Sizer an entry, so it checks conversions to
// optlib.W against Sizer, and relies on that check (D5 of F35). It is built
// with optb, whose trust file gives Sizer none, which it reports.
package opta // want `the trust files of this build give entries to different interfaces, against which values are checked where they are converted: the proofs of package opta count optlibx.Sizer, which .*opta/vego-trusted.yaml gives entries, and those of package optb do not`

import (
	"optb"
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

// S is an io.Writer of package opta.
type S interface{ optlib.W }

// Use2 takes what optb makes under a type optb never names here (F16 of the
// review of S1): per-type records would not have compared them.
//
// @Ensures n >= 0
func Use2() (n int) {
	var s S = optb.Make2()
	if z, ok := s.(optlibx.Sizer); ok {
		n = z.Size()
	}
	return n
}
