// Package exitslib has functions whose contracts come from the trust file
// of the corpus, some of which end the process.
package exitslib

import "os"

// Stop ends the process.
func Stop() { os.Exit(1) }

// MayStop ends the process for a negative n, and returns n otherwise.
func MayStop(n int) int {
	if n < 0 {
		os.Exit(1)
	}
	return n
}

// Both is given an entry that says it never returns and returns 1.
func Both() int { os.Exit(1); return 1 }

// FalseOnly is given an entry that says it never returns, without saying
// how.
func FalseOnly() { os.Exit(1) }

// T has a method given an entry with exits.
type T struct{}

// Halt ends the process.
func (*T) Halt() { os.Exit(1) }
