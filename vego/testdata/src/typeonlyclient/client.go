// Package typeonlyclient reads the clocks of typeonlylib.
package typeonlyclient

import "typeonlylib"

// Positive relies on the contract of Clock.
//
// @Ensures r > 0
func Positive(n int) (r int) {
	if typeonlylib.Now == nil { // want `vego: cannot verify Positive: typeonlylib.Now cannot be relied on: its initialiser does not verify`
		return 1
	}
	return typeonlylib.Now()
}

// PositiveGood reads the one that meets it.
//
// @Ensures r > 0
func PositiveGood(n int) (r int) {
	if typeonlylib.Good == nil {
		return 1
	}
	return typeonlylib.Good()
}
