// Package pathstore stores, through the path of a group variable, a
// reference to memory something else holds (F36 of the review of part 2
// of package-level variables). Before, the invariant was relied on, and a
// write through the other reference broke it: after link(p) and spoil(p),
// or across(spoiler{q}) after link(q), peek returned -1.
package pathstore

import "io"

// Entry is a linked entry.
type Entry struct {
	n    int
	next *Entry
}

// @Invariant e != nil And e.next != nil And e.next.n >= 0 // want `^vego: the invariant of e cannot be relied on: the store through e at p.go:\d+ puts there a reference to memory that it did not make where it stands, which something else may hold, so a write through another reference could break the invariant without naming the variable$`
var e = &Entry{next: &Entry{n: 1}}

// link stores p, which its caller holds, under e.
//
// @Requires p != nil And p.n >= 0
// @Modifies e
// @Ensures True
func link(p *Entry) {
	if e != nil {
		e.next = p
	}
}

// relink stores memory it makes where it stands.
//
// @Modifies e
// @Ensures True
func relink() {
	if e != nil {
		e.next = &Entry{n: 2}
	}
}

// spoil writes through what it is handed.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func spoil(p *Entry) { p.n = -1 }

// across writes through w.
//
// @Requires w != nil
// @Modifies e, w
// @Ensures True
func across(w io.Writer) {
	w.Write([]byte("x"))
	if e != nil {
		e.n = 0
	}
}
