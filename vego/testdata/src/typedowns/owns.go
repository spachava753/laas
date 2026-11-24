// Package typedowns takes parts of owners out of errors (F7 of the design
// review of F33): what an error holds is part of it, so a part of an owner
// put into an error and asserted out again is still the owner's.
package typedowns

import (
	"fmt"
	"io"
)

// Child is owned by an S.
type Child struct{ n int }

// S owns its child.
//
// @Owns child
type S struct{ child *Child }

// PartErr holds a pointer it does not export.
type PartErr struct{ p *Child }

// @Ensures True
func (e PartErr) Error() (s string) { return "part" }

// Holder keeps a child.
type Holder struct{ P *Child }

// ErrHolder keeps an error.
type ErrHolder struct{ Err error }

// @Requires s != nil And h != nil
// @Modifies h
// @Ensures True
func StoreAsserted(s *S, h *Holder) {
	var e error = PartErr{p: s.child}
	if pe, ok := e.(PartErr); ok {
		h.P = pe.p // want `pe.p is memory that s owns, stored into memory at owns.go:\d+:\d+; it may be read and written here, but not kept elsewhere`
	}
}

// @Requires s != nil And h != nil
// @Modifies h
// @Ensures True
func StoreOneResult(s *S, h *Holder) {
	var e error = PartErr{p: s.child}
	h.P = e.(PartErr).p // want `e.\(PartErr\).p is memory that s owns, stored into memory at owns.go:\d+:\d+`
}

// @Requires s != nil And h != nil
// @Modifies h
// @Ensures True
func StoreSwitched(s *S, h *Holder) {
	var e error = PartErr{p: s.child}
	switch pe := e.(type) {
	case PartErr:
		h.P = pe.p // want `pe.p is memory that s owns, stored into memory at owns.go:\d+:\d+`
	}
}

// @Requires s != nil And h != nil
// @Modifies h
// @Ensures True
func StoreError(s *S, h *ErrHolder) {
	var e error = PartErr{p: s.child}
	h.Err = e // want `e is memory that s owns, stored into memory at owns.go:\d+:\d+`
}

// ReturnsPart returns an error it made that holds a part of s, which no
// contract can place within s: refused, since a caller that is not
// verified could take the part out and keep it (F19 of the review of S3).
// Its summary still says so, and a verified caller may not keep it.
//
// @Requires s != nil
// @Ensures err != nil
func ReturnsPart(s *S) (err error) {
	return PartErr{p: s.child} // want `ReturnsPart returns memory that s owns, held in an error, which no contract can place within s; return a copy`
}

// @Requires s != nil And h != nil
// @Modifies h
// @Ensures True
func KeepsReturned(s *S, h *Holder) {
	if pe, ok := ReturnsPart(s).(PartErr); ok {
		h.P = pe.p // want `pe.p is memory that s owns, stored into memory at owns.go:\d+:\d+`
	}
}

// PE is an error that holds a line.
type PE struct{ Line int }

// @Ensures True
func (e *PE) Error() (s string) { return "pe" }

// @Requires w != nil And pe != nil
// @Modifies w, pe
// @Ensures True
func write(w io.Writer, pe *PE) {
	pe.Line = 0
	_, _ = w.Write(nil)
}

// Beside hands a pointer that the error it was given holds beside a
// writer: what the error holds is reached only through an interface
// value, so nothing keeps it apart from what the writer writes.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func Beside(w io.Writer, err error) {
	switch pe := err.(type) {
	case *PE:
		if pe != nil {
			write(w, pe) // want `the footprint of what is passed to write as w may hold memory that what is passed as pe reaches, and write relies on it not doing so: it comes from a type assertion` `write may modify pe, which Beside may not modify`
		}
	}
}

// BesideAsserted does the same with the two-result form.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func BesideAsserted(w io.Writer, err error) {
	if pe, ok := err.(*PE); ok && pe != nil {
		write(w, pe) // want `the footprint of what is passed to write as w may hold memory that what is passed as pe reaches, and write relies on it not doing so: it comes from a type assertion` `write may modify pe, which BesideAsserted may not modify`
	}
}

// Report owns its writer.
//
// @Owns out
type Report struct{ out *Child }

// fail returns an error that may hold what it is handed.
func fail(c *Child) (err error) { return nil }

// PassesOn returns the error of a call made on what r owns, which may hold
// it: what code that is not verified does with such an error is in "What
// a proof assumes" (F19 of the review of S3).
//
// @Requires r != nil
// @Ensures True
func PassesOn(r *Report) (err error) {
	err = fail(r.out)
	return err
}

// MadeThenPassed returns an error that may be one it made from a part of r
// or one a call returned: refused, since one assignment makes it.
//
// @Requires r != nil
// @Ensures True
func MadeThenPassed(r *Report, c bool) (err error) {
	err = fail(r.out)
	if c {
		err = PartErr{p: r.out}
	}
	return err // want `MadeThenPassed returns memory that r owns, held in an error, which no contract can place within r; return a copy`
}

// Cell is an error whose errors have a known origin, typed, and that an
// owner owns: a part of the owner can then be wrapped by fmt.Errorf, whose
// result holds what %w wraps.
type Cell struct{ n int }

// @Ensures True
func (c *Cell) Error() (s string) { return "cell" }

// Box owns its cell.
//
// @Owns cell
type Box struct{ cell *Cell }

// @Requires b != nil And h != nil
// @Modifies h
// @Ensures True
func StoreWrapped(b *Box, h *ErrHolder) {
	var e error = b.cell
	h.Err = fmt.Errorf("wrapped: %w", e) // want `fmt.Errorf\("wrapped: %w", e\) is memory that b owns, stored into memory at owns.go:\d+:\d+`
}

// @Requires b != nil
// @Ensures True
func ReturnsWrapped(b *Box) (err error) {
	var e error = b.cell
	return fmt.Errorf("wrapped: %w", e) // want `ReturnsWrapped returns memory that b owns, held in an error, which no contract can place within b; return a copy`
}

// @Requires b != nil
// @Ensures r
func FormatsPart(b *Box) (r bool) {
	var e error = b.cell
	return fmt.Errorf("part: %v", e) != nil
}
