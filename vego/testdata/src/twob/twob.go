// Package twob relies on the entry of its module only through what a
// trusted function claims of the sinks it runs.
package twob

import "twoentrieslib"

func run(s twoentrieslib.Sink) (r int) { return s.Put(1) }

// @Requires s != nil
// @Ensures r >= 0
func F(s twoentrieslib.Sink) (r int) {
	return run(s)
}
