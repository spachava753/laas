// r25: code of another package reaches a method of the package by assertion.
package p

import "cycles/r25/q"

// T has a method that q finds by assertion.
type T struct{}

func (T) Hello() int { return F() }

// @Ensures True
func F() (n int) {
	return q.Run(T{}) // want `this\ call\ may\ not\ end:\ F\ hands\ T\{\}\ to\ q\.Run\(T\{\}\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T\.Hello,\ T\.Hello\ calls\ F\ at\ p\.go:\d+:\d+`
}
