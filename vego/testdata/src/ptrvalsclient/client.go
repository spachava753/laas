// Package ptrvalsclient calls ptrvalslib.Inc through pointers it makes.
package ptrvalsclient

import "ptrvalslib"

// Twice increments p twice through the other package.
//
// @Requires p != nil And *p < 100
// @Modifies p
// @Ensures *p' = old(*p) + 2
func Twice(p *int) {
	ptrvalslib.Inc(p)
	// @Assert *p = old(*p) + 1
	ptrvalslib.Inc(p)
}

// Stale claims that what p points to is unchanged by the call.
//
// @Requires p != nil And *p < 100
// @Modifies p
// @Ensures *p' = *p
func Stale(p *int) {
	ptrvalslib.Inc(p)
} // want `vego: postcondition may not hold: \*p' = \*p`

// Local increments a local through the other package.
//
// @Ensures r = 1
func Local() (r int) {
	x := 0
	ptrvalslib.Inc(&x)
	return x
}
