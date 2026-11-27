// Package abovep calls M of an interface value that abover, which imports
// it, wraps around a QT in code that is not verified. abovep cannot see
// abover; abover sees QT.N, which calls back into Y, as what T.M may run,
// and reports the cycle at T.M (F1 (a) of the review of the design of F43).
package abovep

// I is called.
type I interface {
	// @Ensures True
	M()
}

// J is wrapped.
type J interface {
	// @Ensures True
	N()
}

// Made is set by code that is not verified.
var Made I

// SetMade is not verified.
func SetMade(i I) { Made = i }

// @Requires i != nil
// @Ensures True
func Y(i I) { i.M() }

// QT calls back into Y.
type QT struct{}

// @Ensures True
func (QT) N() {
	if Made != nil {
		Y(Made)
	}
}
