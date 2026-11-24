// Package madehere stores into a group new memory that holds a reference
// to memory something else holds, at depth (F37 of the review of part 2 of
// package-level variables). Before, each invariant was relied on, and a
// write through the held reference broke it.
package madehere

// Entry is a linked entry.
type Entry struct {
	n    int
	next *Entry
}

// @Invariant a != nil And a.next != nil And a.next.next != nil And a.next.next.n >= 0 // want `^vego: the invariant of a cannot be relied on: the store through a at m.go:\d+ puts there a reference to memory that it did not make where it stands, which something else may hold, so a write through another reference could break the invariant without naming the variable$`
var a = &Entry{next: &Entry{next: &Entry{n: 1}}}

// linkA stores a new entry that holds p.
//
// @Requires p != nil And p.n >= 0
// @Modifies a
// @Ensures True
func linkA(p *Entry) {
	if a != nil {
		a.next = &Entry{next: p}
	}
}

// @Invariant b != nil And b.next != nil And b.next.n >= 0 // want `^vego: the invariant of b cannot be relied on: the use of b at m.go:\d+ lets a reference to what it refers to out of it, so a write through another reference could break the invariant without naming the variable$`
var b = &Entry{next: &Entry{n: 1}}

// relinkB assigns b a new entry that holds p.
//
// @Requires p != nil And p.n >= 0
// @Modifies b
// @Ensures True
func relinkB(p *Entry) { b = &Entry{next: p} }

var shared = &Entry{n: 1}

// spoilShared writes what shared points to.
//
// @Requires shared != nil
// @Modifies shared
// @Ensures True
func spoilShared() { shared.n = -1 }

// @Invariant c != nil And c.next != nil And c.next.n >= 0 // want `^vego: the invariant of c cannot be relied on: the initialiser of c does not make what it refers to, so something else may hold it$`
var c = &Entry{next: shared}

// relinkFresh stores new memory, made where it stands at every depth.
//
// @Modifies d
// @Ensures True
func relinkFresh() {
	if d != nil {
		d.next = &Entry{next: &Entry{n: 3}}
	}
}

// @Invariant d != nil
var d = &Entry{next: &Entry{n: 1}}
