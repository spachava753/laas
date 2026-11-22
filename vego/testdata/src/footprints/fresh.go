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
	s.Put(nil) // want `s.Put may modify the footprint of s, which WrapAndPutUnlisted may not modify`
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
	p.A = 1 // want `p.A is assigned, which WritesBoxUnlisted may not modify; it is memory that boxIn returned`
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
