// Package iowrap uses the shipped entries of the functions of io that keep
// the readers and writers they are given.
package iowrap

import (
	"io"

	"keepslib"
)

// Copies reads once from r and writes what it read to w as well.
//
// @Requires r != nil And w != nil
// @Ensures 0 <= n And n <= 16
func Copies(r io.Reader, w io.Writer) (n int, err error) {
	t := io.TeeReader(r, w)
	return t.Read(make([]byte, 16))
}

// TeesToNothing hands TeeReader a writer that may be nil.
//
// @Requires r != nil
// @Ensures True
func TeesToNothing(r io.Reader, w io.Writer) {
	_ = io.TeeReader(r, w) // want `vego: precondition of TeeReader may not hold: w != nil`
}

// Closes reads through a closer that closes nothing and closes it.
//
// @Requires r != nil
// @Ensures True
func Closes(r io.Reader) (err error) {
	rc := io.NopCloser(r)
	defer rc.Close()
	_, err = rc.Read(make([]byte, 16))
	return err
}

// ClosesTwice closes a closer twice, which its entry does not allow.
//
// @Requires r != nil
// @Ensures True
func ClosesTwice(r io.Reader) {
	rc := io.NopCloser(r)
	_ = rc.Close()
	_ = rc.Close() // want `vego: precondition of rc.Close may not hold: ~closed\(c\)`
}

// ClosesApart closes a closer over a reader that is itself a closer, and
// closes that one too: the closer NopCloser returns is new, so closing it
// leaves the other open.
//
// @Requires orig != nil And ~closed(orig)
// @Modifies orig
// @Ensures closed(orig')
func ClosesApart(orig io.ReadCloser) {
	rc := io.NopCloser(orig)
	_ = rc.Close()
	_ = orig.Close()
}

// Limits reads at most n bytes of r.
//
// @Requires r != nil
// @Ensures 0 <= got And got <= 8
func Limits(r io.Reader, n int64) (got int, err error) {
	l := io.LimitReader(r, n)
	return l.Read(make([]byte, 8))
}

// Joins reads from two readers in turn.
//
// @Requires a != nil And b != nil
// @Ensures 0 <= n And n <= 4
func Joins(a, b io.Reader) (n int, err error) {
	m := io.MultiReader(a, b)
	return m.Read(make([]byte, 4))
}

// JoinsAll reads from the readers of a slice in turn.
//
// @Requires Forall i in [0, |rs|) : rs[i] != nil
// @Ensures True
func JoinsAll(rs []io.Reader) (err error) {
	m := io.MultiReader(rs...)
	_, err = m.Read(make([]byte, 4))
	return err
}

// JoinsSome hands MultiReader a slice that may hold nil.
//
// @Ensures True
func JoinsSome(rs []io.Reader) {
	_ = io.MultiReader(rs...) // want `vego: precondition of MultiReader may not hold: Forall i in \[0, \|readers\|\) : readers\[i\] != nil`
}

// Copies2 writes p to two writers.
//
// @Requires w1 != nil And w2 != nil
// @Ensures 0 <= n And n <= |p|
func Copies2(w1, w2 io.Writer, p []byte) (n int, err error) {
	m := io.MultiWriter(w1, w2)
	return m.Write(p)
}

// Drained reads by handing a NopCloser of itself to Consume, which runs
// what a closer holds: NopCloser puts code that verified code made into
// an io.ReadCloser, so Consume counts as a call through a value.
type Drained struct{}

// Read hands a closer over a value of its own type to Consume.
//
// @Requires |p| > 0
// @Modifies p
// @Ensures 0 <= n And n <= |p| And err = nil
func (Drained) Read(p []byte) (n int, err error) {
	p[0] = 0
	drain() // want `this call may not end: Drained.Read calls drain at iowrap.go:\d+:\d+, drain hands io.NopCloser\(Drained\{\}\) to keepslib.Consume\(io.NopCloser\(Drained\{\}\)\) at iowrap.go:\d+:\d+, which may run Drained.Read`
	return 1, nil
}

// @Ensures True
func drain() {
	keepslib.Consume(io.NopCloser(Drained{})) // want `cannot\ verify\ drain:\ Read\ may\ call\ through\ a\ function\ value\ or\ an\ interface\ value,\ and\ code\ that\ an\ interface\ value\ runs\ cannot\ do\ that\ yet:\ no\ contract\ of\ a\ function\ type\ or\ of\ a\ method\ of\ an\ interface\ has\ a\ variant,\ so\ nothing\ would\ prove\ that\ such\ calls\ end`
}
