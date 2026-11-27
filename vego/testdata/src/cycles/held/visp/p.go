// Package visp hands visq.F a visr.T, made by code that is not verified
// around a PT, whose N calls back into X: an implementation of visq.I that
// visp can see and visq cannot (F1 (a) of the review of the design of F43).
package visp

import (
	"cycles/held/visq"
	"cycles/held/visr"
)

// PT calls back into X.
type PT struct{}

// @Ensures True
func (PT) N() {
	if Made != nil {
		X(Made) // want `this call may not end: PT.N calls X at p.go:\d+:\d+, X hands i to visq.F\(i\) at p.go:\d+:\d+, which may run PT.N`
	}
}

// Made is set by code that is not verified.
var Made visq.I

// Setup is not verified.
func Setup() { Made = visr.Wrap(PT{}) }

// @Requires i != nil
// @Ensures True
func X(i visq.I) {
	visq.F(i) // want `this call may not end: X hands i to visq.F\(i\) at p.go:\d+:\d+, which may run X`
}
