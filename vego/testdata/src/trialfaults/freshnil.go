package trialfaults

import "io"

// newCloser may return nil; its entry promises only that what it returns
// is new. A nil interface value has no home, so two nil results do not
// make the caller's state contradict itself, as they did when nil had one.
func newCloser() io.ReadCloser { return nil }

// Both results may be nil, and then BothNil returns 2.
//
// @Ensures r = 1
func BothNil() (r int) {
	a := newCloser()
	b := newCloser()
	if a == nil && b == nil {
		return 2 // want `postcondition may not hold: r = 1`
	}
	return 1
}

// @Ensures r = 1 Or r = 2
func EitherNil() (r int) {
	a := newCloser()
	b := newCloser()
	if a == nil && b == nil {
		return 2
	}
	return 1
}
