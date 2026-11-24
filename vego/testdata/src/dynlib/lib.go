// Package dynlib changes its counter through a function value and an
// interface method, which no call by name shows (F25 of the review of
// step 4 of package-level variables).
package dynlib

// Count counts.
var Count int

var hook = func() {
	if Count < 1000 {
		Count++
	}
}

// ViaHook counts through a function value, and is not verified.
func ViaHook() { hook() }

// Bumper counts.
type Bumper interface{ Bump() }

type impl struct{}

// Bump counts, and is not verified.
func (impl) Bump() {
	if Count < 1000 {
		Count++
	}
}

// ViaIface counts through an interface method, and is not verified.
func ViaIface() {
	var b Bumper = impl{}
	b.Bump()
}
