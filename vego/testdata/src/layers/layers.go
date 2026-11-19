// Package layers holds loops that write one struct, or some fields of one,
// and what is known afterwards of other memory: a loop keeps what lies at
// every other position, as a call that writes the same struct does.
package layers

import "sync"

// Point has two fields.
type Point struct{ x, y int }

// @Requires q != nil
// @Modifies q
// @Ensures q.x' = 0 And q.y' = 0
func reset(q *Point) {
	q.x, q.y = 0, 0
}

// @Requires q != nil
// @Modifies q.x
// @Ensures q.x' = 0
func zeroX(q *Point) {
	q.x = 0
}

// LoopPoint keeps the fields of another point. Two distinct pointers to
// points may lie in one allocation, but never four bytes apart.
//
// @Requires p != nil And q != nil And p != q And 0 <= n <= 10
// @Modifies q
// @Ensures p.x' = p.x And p.y' = p.y
func LoopPoint(p, q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		reset(q)
	}
}

// LoopPtr keeps the state of another mutex.
//
// @Requires p != nil And q != nil And p != q And held(p) And ~held(q) And 0 <= n <= 10
// @Modifies q
// @Ensures held(p')
func LoopPtr(p, q *sync.Mutex, n int) {
	// @Invariant 0 <= i <= n And ~held(q)
	// @Variant n - i
	for i := 0; i < n; i++ {
		q.Lock()
		q.Unlock()
	}
}

// OtherField keeps the field the loop does not write.
//
// @Requires q != nil And 0 <= n <= 10
// @Modifies q.x
// @Ensures q.y' = q.y
func OtherField(q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		zeroX(q)
	}
}

// Every function below would be accepted if the loop kept too much.

// WrittenField does not keep the field the loop writes.
//
// @Requires q != nil And 0 <= n <= 10
// @Modifies q.x
// @Ensures q.x' = q.x
func WrittenField(q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		zeroX(q)
	}
} // want `vego: postcondition may not hold: q.x' = q.x`

// MayBeEqual writes a point that may be the other one.
//
// @Requires p != nil And q != nil And 0 <= n <= 10
// @Modifies q
// @Ensures p.x' = p.x
func MayBeEqual(p, q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		reset(q)
	}
} // want `vego: postcondition may not hold: p.x' = p.x`

// Walk writes each point of a slice through a pointer the loop assigns.
//
// @Requires p != nil And |s| <= 10
// @Modifies s
// @Ensures p.x' = p.x
func Walk(p *Point, s []Point) {
	// @Invariant 0 <= i <= |s|
	for i := range s {
		q := &s[i]
		q.x = 0
	}
} // want `vego: postcondition may not hold: p.x' = p.x`

// IntoArray writes one point of a slice through a pointer to it, and the
// point is not kept.
//
// @Requires |s| >= 2 And 0 <= n <= 10
// @Modifies s
// @Ensures s[1].x' = s[1].x
// @Ensures s[0].x' = s[0].x
func IntoArray(s []Point, n int) {
	q := &s[0]
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		q.x = 1
	}
} // want `vego: postcondition may not hold: s\[0\].x' = s\[0\].x`

// ThroughElement writes through an element of a slice that a pointer may
// point into.
//
// @Requires p != nil And |s| >= 1 And 0 <= n <= 10
// @Modifies s
// @Ensures p.x' = p.x
func ThroughElement(p *Point, s []Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		s[0].x = 1
	}
} // want `vego: postcondition may not hold: p.x' = p.x`

// DirectWrite writes a field without a call.
//
// @Requires p != nil And q != nil And 0 <= n <= 10
// @Modifies q.x
// @Ensures p.x' = p.x
func DirectWrite(p, q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		q.x = i
	}
} // want `vego: postcondition may not hold: p.x' = p.x`

// Nested writes in an inner loop.
//
// @Requires p != nil And q != nil And 0 <= n <= 10
// @Modifies q.x
// @Ensures p.x' = p.x
func Nested(p, q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		// @Invariant 0 <= j <= n
		// @Variant n - j
		for j := 0; j < n; j++ {
			q.x = j
		}
	}
} // want `vego: postcondition may not hold: p.x' = p.x`

// NestedApart keeps the other point through both loops.
//
// @Requires p != nil And q != nil And p != q And 0 <= n <= 10
// @Modifies q.x
// @Ensures p.x' = p.x And p.y' = p.y
func NestedApart(p, q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		// @Invariant 0 <= j <= n
		// @Variant n - j
		for j := 0; j < n; j++ {
			q.x = j
		}
	}
}

// Literal writes in a function literal called in the loop.
//
// @Requires p != nil And q != nil And 0 <= n <= 10
// @Modifies q.x
// @Ensures p.x' = p.x
func Literal(p, q *Point, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		func() { q.x = i }()
	}
} // want `vego: postcondition may not hold: p.x' = p.x`

// Guarded holds a mutex and a field.
type Guarded struct {
	mu sync.Mutex
	n  int
}

// StateAndField writes the field of one struct and keeps the state of the
// mutex beside it, which lies at another position of another region; the
// field of a struct that may be the same one is not kept.
//
// @Requires g != nil And h != nil And held(g.mu) And 0 <= k <= 10
// @Modifies h.n
// @Ensures held(g.mu')
// @Ensures g.n' = g.n
func StateAndField(g, h *Guarded, k int) {
	// @Invariant 0 <= i <= k
	// @Variant k - i
	for i := 0; i < k; i++ {
		h.n = i
	}
} // want `vego: postcondition may not hold: g.n' = g.n`

// LockedState locks one mutex in a loop and keeps the state of another,
// which differs from it since one is held and the other is not.
//
// @Requires g != nil And h != nil And held(g.mu) And ~held(h.mu) And 0 <= k <= 10
// @Modifies g.mu, h.mu
// @Ensures ~held(g.mu') And ~held(h.mu')
func LockedState(g, h *Guarded, k int) {
	// @Invariant 0 <= i <= k And ~held(h.mu)
	// @Variant k - i
	for i := 0; i < k; i++ {
		h.mu.Lock()
		h.mu.Unlock()
	}
	g.mu.Unlock()
}

// Outer holds two points.
type Outer struct{ a, b Point }

// Halves writes one point of a struct and keeps the other, whose fields lie
// in the same regions at other positions.
//
// @Requires o != nil And 0 <= n <= 10
// @Modifies o.a
// @Ensures o.b.x' = o.b.x
// @Ensures o.a.y' = o.a.y
func Halves(o *Outer, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		reset(&o.a)
	}
} // want `vego: postcondition may not hold: o.a.y' = o.a.y`

// OtherOuter writes the first point of a struct that may be the other one.
//
// @Requires p != nil And q != nil And 0 <= n <= 10
// @Modifies q.a
// @Ensures p.a.x' = p.a.x
func OtherOuter(p, q *Outer, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		reset(&q.a)
	}
} // want `vego: postcondition may not hold: p.a.x' = p.a.x`

// Embedding has a point as an embedded field.
type Embedding struct {
	z int
	Point
}

// Promoted writes the embedded point, which lies after z.
//
// @Requires e != nil And 0 <= n <= 10
// @Modifies e.Point
// @Ensures e.z' = e.z
// @Ensures e.x' = e.x
func Promoted(e *Embedding, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		reset(&e.Point)
	}
} // want `vego: postcondition may not hold: e.x' = e.x`

// Link points to an outer struct.
type Link struct {
	to *Outer
	n  int
}

// Behind writes a point behind a second pointer, which the variable does
// not point into, so the loop keeps only what Modifies does not list.
//
// @Requires l != nil And l.to != nil And 0 <= n <= 10
// @Modifies l.to
// @Ensures l.n' = l.n
// @Ensures l.to.b.x' = l.to.b.x
func Behind(l *Link, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		reset(&l.to.a)
	}
} // want `vego: postcondition may not hold: l.to.b.x' = l.to.b.x`
