// Package distinct holds the fact between struct values: two struct values
// of one type are one value or lie at least the size of the type apart, so
// a write of one keeps every field of the other, also when the type holds
// two fields of one struct type.
package distinct

// Inner is one point.
type Inner struct{ X int }

// Pair holds two points by value.
type Pair struct{ A, B Inner }

// @Requires p != nil
// @Modifies p
// @Ensures True
func reset(p *Pair) {
	p.A.X = 0
	p.B.X = 0
}

// KeepsPairCall writes p by a call and keeps q, which is another Pair.
//
// @Requires p != nil And q != nil And p != q
// @Modifies p
// @Ensures q.B.X' = q.B.X And q.A.X' = q.A.X
func KeepsPairCall(p, q *Pair) {
	reset(p)
}

// MayBeSamePair is KeepsPairCall where q may be p.
//
// @Requires p != nil And q != nil
// @Modifies p
// @Ensures q.B.X' = q.B.X
func MayBeSamePair(p, q *Pair) {
	reset(p)
} // want `postcondition may not hold: q.B.X' = q.B.X`

// KeepsPairInLoop writes p in a loop and keeps q.
//
// @Requires p != nil And q != nil And p != q And k >= 0
// @Modifies p
// @Ensures q.B.X' = q.B.X And q.A.X' = q.A.X
func KeepsPairInLoop(p, q *Pair, k int) {
	// @Variant k - i
	for i := 0; i < k; i++ {
		reset(p)
	}
}

// KeepsPairWrite writes one field of p directly and keeps q.
//
// @Requires p != nil And q != nil And p != q
// @Modifies p
// @Ensures q.A.X' = q.A.X
func KeepsPairWrite(p, q *Pair) {
	p.B.X = 1
}

// KeepsField writes the field B of p, listed as a path, by a call and
// keeps the field A of q.
//
// @Requires p != nil And q != nil And p != q
// @Modifies p.B
// @Ensures q.A.X' = q.A.X
func KeepsField(p, q *Pair) {
	setInner(&p.B)
}

// @Requires in != nil
// @Modifies in
// @Ensures True
func setInner(in *Inner) {
	in.X = 2
}

// InnerOfPair writes p and reads an Inner that may be one of p's points.
//
// @Requires p != nil And in != nil
// @Modifies p
// @Ensures in.X' = in.X
func InnerOfPair(p *Pair, in *Inner) {
	reset(p)
} // want `postcondition may not hold: in.X' = in.X`

// Outer holds a point and a number.
type Outer struct {
	In Inner
	Z  int
}

// InnerOfOuter writes o and reads an Inner that may be the one o holds,
// which lies where o does: two struct types at one position.
//
// @Requires o != nil And in != nil
// @Modifies o
// @Ensures in.X' = in.X
func InnerOfOuter(o *Outer, in *Inner) {
	o.In.X = 3
} // want `postcondition may not hold: in.X' = in.X`

// Twin has the fields of Pair, so a *Twin and a *Pair may be one struct.
type Twin struct{ A, B Inner }

// TwinOfPair writes p and reads a Twin that may be p, converted.
//
// @Requires p != nil And t != nil
// @Modifies p
// @Ensures t.A.X' = t.A.X
func TwinOfPair(p *Pair, t *Twin) {
	reset(p)
} // want `postcondition may not hold: t.A.X' = t.A.X`

// Zeroer zeroes what it holds.
type Zeroer interface {
	// @Receiver z
	// @Modifies z
	// @Ensures True
	Zero()
}

// @Requires p != nil
// @Modifies p
// @Ensures True
func (p *Pair) Zero() {
	p.A.X = 0
	p.B.X = 0
}

// KeepsPairIface writes p through a converted value and keeps q.
//
// @Requires p != nil And q != nil And p != q
// @Modifies p
// @Ensures q.B.X' = q.B.X And q.A.X' = q.A.X
func KeepsPairIface(p, q *Pair) {
	var z Zeroer = p
	z.Zero()
}

// MayBeSameIface is KeepsPairIface where q may be p.
//
// @Requires p != nil And q != nil
// @Modifies p
// @Ensures q.A.X' = q.A.X
func MayBeSameIface(p, q *Pair) {
	var z Zeroer = p
	z.Zero()
} // want `postcondition may not hold: q.A.X' = q.A.X`

// Counter counts.
type Counter struct{ N, M int }

// Recorder records a name.
type Recorder interface {
	// @Receiver r
	// @Requires |name| <= 100
	// @Modifies r
	// @Ensures True
	Record(name string)
}

// @Requires c != nil
// @Modifies c
// @Ensures True
func (c *Counter) Record(name string) {
	if c.N < 1000 {
		c.N++
	}
}

// KeepsOtherCounter writes the first counter through an interface and
// keeps the second, which is another counter (the orchestrator's probe).
//
// @Requires |ts| = 2 And ts[0] != nil And ts[1] != nil And ts[0] != ts[1]
// @Modifies ts[0]
// @Ensures ts[1].N' = ts[1].N And ts[1].M' = ts[1].M
func KeepsOtherCounter(ts []*Counter) {
	var r Recorder = ts[0]
	r.Record("x")
}

// MayBeSameCounter is KeepsOtherCounter where the two may be one.
//
// @Requires |ts| = 2 And ts[0] != nil And ts[1] != nil
// @Modifies ts[0]
// @Ensures ts[1].N' = ts[1].N
func MayBeSameCounter(ts []*Counter) {
	var r Recorder = ts[0]
	r.Record("x")
} // want `postcondition may not hold: ts\[1\].N' = ts\[1\].N`

// AdjacentPairs writes the first of two neighbouring elements of a slice of
// Pairs, which lie exactly the size of a Pair apart, and claims the second
// changed: false, and refused; a fact that kept them further apart would
// make the state contradictory and prove it.
//
// @Requires |ps| = 2
// @Modifies ps
// @Ensures r = 1
func AdjacentPairs(ps []Pair) (r int) {
	ps[1].A.X = 5
	reset(&ps[0])
	if ps[1].A.X == 5 {
		return 2 // want `postcondition may not hold: r = 1`
	}
	return 1
}

// SecondPoint writes the second point of p and reads an Inner that is not
// the first one, so it may be the second: refused, whatever two Pairs keep
// apart.
//
// @Requires p != nil And in != nil And in != &p.A
// @Modifies p
// @Ensures in.X' = in.X
func SecondPoint(p *Pair, in *Inner) {
	p.B.X = 4
} // want `postcondition may not hold: in.X' = in.X`
