// Package twoc has no entry for twoentrieslib.Sink, so its trusted
// function that returns a sink is not asked to vouch for it.
package twoc

import "twoentrieslib"

// Counter counts.
type Counter struct {
	N int
}

type lineSink struct{ c *Counter }

func (s lineSink) Put(x int) (y int) {
	s.c.N++
	return 0
}

// newSink returns a sink that counts into c; it writes nothing itself.
func newSink(c *Counter) (s twoentrieslib.Sink) { return lineSink{c} }

// @Requires c != nil
// @Ensures True
func Make(c *Counter) (s twoentrieslib.Sink) {
	return newSink(c)
}
