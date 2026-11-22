package footprints

import "bufio"

// MakeAndKeep writes through a new sink, whose footprint is new, and keeps
// a pair it was handed, which existed before.
//
// @Requires f != nil And q != nil
// @Ensures q.A' = q.A
func MakeAndKeep(f Factory, q *Pair) {
	s, _ := f.Make()
	s.Put(nil)
}

// wrapSink is trusted to make a sink that writes new memory or what the
// sink it keeps writes.
func wrapSink(w Sink) (s Sink) { return w }

// WrapAndPut writes through a sink made over w, which writes new memory
// or what w writes, and keeps a pair handed in beside w.
//
// @Requires w != nil And q != nil
// @Modifies w
// @Ensures q.A' = q.A
func WrapAndPut(w Sink, q *Pair) {
	s := wrapSink(w)
	s.Put(nil)
}

// WrapAndPutUnlisted writes through a sink made over w, which may write
// what w writes, without listing w.
//
// @Requires w != nil
// @Ensures True
func WrapAndPutUnlisted(w Sink) {
	s := wrapSink(w)
	s.Put(nil) // want `s.Put may modify the footprint of s, which WrapAndPutUnlisted may not modify; it may lie in the footprint of w, as the contract of wrapSink at fresh.go:36:7 says; list w in a // @Modifies clause`
}

// NotAFootprint says that a pair may lie in what another pair writes.
type NotAFootprint interface {
	// @Ensures fresh(p, q) // want `fresh\(p, q\): q is not an interface value whose methods write behind it, so it has no footprint for p to lie in`
	Make(q *Pair) (p *Pair)
}

// boxIn is trusted to return a pair that is new or lies in what w writes.
func boxIn(w Sink) (p *Pair) { return &Pair{} }

// WritesBox writes the pair, which w's footprint may hold.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func WritesBox(w Sink) {
	p := boxIn(w)
	p.A = 1
}

// WritesBoxUnlisted writes the pair without listing w.
//
// @Requires w != nil
// @Ensures True
func WritesBoxUnlisted(w Sink) {
	p := boxIn(w)
	p.A = 1 // want `p.A is assigned, which WritesBoxUnlisted may not modify; it is memory that boxIn returned, which its contract places in the footprint of w when it is not new; list w in a // @Modifies clause`
}

// tableOf is trusted to return a map that lies in what w writes.
func tableOf(w Sink) (m map[int]int) { return map[int]int{} }

// WritesTable writes the map, which lies in w's footprint.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func WritesTable(w Sink) {
	m := tableOf(w)
	m[1] = 2
}

// WritesTableUnlisted writes the map without listing w.
//
// @Requires w != nil
// @Ensures True
func WritesTableUnlisted(w Sink) {
	m := tableOf(w)
	m[1] = 2 // want `m\[1\] is assigned, which WritesTableUnlisted may not modify`
}

// spareOf is trusted to return a slice that lies within what bw owns.
func spareOf(bw *bufio.Writer) (p []byte) { return nil }

// WritesSpare writes into what bw owns, which its Modifies covers.
//
// @Requires bw != nil
// @Modifies bw
// @Ensures True
func WritesSpare(bw *bufio.Writer) {
	p := spareOf(bw)
	if len(p) > 0 {
		p[0] = 1
	}
}

// WritesSpareUnlisted writes into what bw owns without listing bw.
//
// @Requires bw != nil
// @Ensures True
func WritesSpareUnlisted(bw *bufio.Writer) {
	p := spareOf(bw)
	if len(p) > 0 {
		p[0] = 1 // want `p\[0\] is assigned, which WritesSpareUnlisted may not modify; it is memory that spareOf returned, which its contract places within bw`
	}
}

// SinkMaker makes a sink whose footprint is new.
//
// @Ensures s != nil And fresh(s)
type SinkMaker func() (s Sink)

// UsesMaker writes through what a maker made, which holds nothing old.
//
// @Requires m != nil And q != nil
// @Ensures q.A' = q.A
func UsesMaker(m SinkMaker, q *Pair) {
	s := m()
	s.Put(nil)
}

// putBeside writes through w and is handed a map beside it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func putBeside(w Sink, m map[int]int) {
	w.Put(nil)
}

// PassesTable hands putBeside a map that lies in w's footprint beside w.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func PassesTable(w Sink) {
	m := tableOf(w)
	putBeside(w, m) // want `the footprint of what is passed to putBeside as w may hold memory that what is passed as m reaches, and putBeside relies on it not doing so: it comes from the call of tableOf at fresh.go:145:7, whose contract places it within w, which may hold memory a writer writes`
}

// Tabler hands out a table of its own, which it may make on the first call.
type Tabler interface {
	// @Receiver r
	// @Modifies r
	// @Ensures m != nil And within(m, r)
	Table() (m map[int]*Pair)
}

// StoresInTable writes into the table r hands out, which lies in r's
// footprint.
//
// @Requires r != nil And q != nil
// @Modifies r
// @Ensures True
func StoresInTable(r Tabler, q *Pair) {
	m := r.Table()
	m[0] = q
}

// grownTable is trusted to write w and return a map in its footprint.
func grownTable(w Sink) (m map[int]int) { return map[int]int{} }

// WritesGrown writes into a map that a call placed in the footprint of w
// as the call grew it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func WritesGrown(w Sink) {
	m := grownTable(w)
	m[1] = 2
}

// Viewer names its receiver only to place a result within it.
type Viewer interface {
	// @Receiver r
	// @Ensures m != nil -> within(m, r)
	Peek() (m map[int]int)

	// @Receiver r
	// @Modifies r
	// @Ensures True
	Put()
}

// pairTable is trusted to return a table that lies in w's footprint.
func pairTable(w Sink) (m map[int]*Pair) { return map[int]*Pair{} }

// StoreThenPut stores a pair into a table that w handed out, and writes
// through w, which is assumed not to write through what verified code
// stored there.
//
// @Requires w != nil And q != nil
// @Modifies w
// @Ensures q.A' = q.A
func StoreThenPut(w Sink, q *Pair) {
	m := pairTable(w)
	m[0] = q
	w.Put(nil)
}
