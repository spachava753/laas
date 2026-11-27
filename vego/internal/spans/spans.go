// Package spans holds the stretches of an allocation that vego compares
// with the positions of the cells of a region (F42, step 3).
//
// Every location in an allocation has a byte address. A region at byte
// addresses (the place region of a type, the region of a field, a region
// of states) has a cell at the byte address b of its first byte. An elem
// region, whose cells are the elements of arrays of one type of n bytes
// each, has a cell at ⌊b/n⌋: for the array of a slice of such elements
// that is the element's index, and for the run of such an array inside a
// struct it is the floor of F36. A stretch is a range of positions of one
// of these kinds: of bytes, or of elements of one size.
//
// Two numbers that count different things must not be compared. A Span
// keeps its numbers to itself, and In is the only way to the positions it
// holds in a region, so code that compares the stretch of a struct with
// positions of the elements of an array inside it without the floor does
// not compile. The elements inside a stretch of bytes [lo, hi), which is
// made of whole values and so never splits an element, lie at the
// positions [⌊lo/n⌋, ⌊hi/n⌋): an element at b has ⌊b/n⌋ in it exactly when
// lo <= b and b + n <= hi, since every other element of the allocation
// lies whole before lo or whole after hi.
package spans

import (
	"fmt"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A Span is a range of positions in an allocation, counted in units of
// unit bytes: bytes (1), or the elements of an array, each of unit bytes.
// arr is set for the stretch of a box whose pointer's #arr is not known: a
// place of one byte when arr is false, an element of unit bytes when it is
// true. The zero Span is no stretch: a map, a row, or what is not known.
type Span struct {
	lo, hi *logic.Term
	unit   int64
	arr    *logic.Term
}

// A Region says how a region counts the positions of its cells: Elem is
// set for an elem region, whose cells are Size bytes each, and clear for a
// region at byte addresses.
type Region struct {
	Elem bool
	Size int64
}

// AtBytes is a region at byte addresses.
var AtBytes = Region{}

// Bytes returns the stretch of byte addresses [lo, hi).
func Bytes(lo, hi *logic.Term) Span {
	return Span{lo: lo, hi: hi, unit: 1}
}

// Elements returns the stretch of the elements [lo, hi) of an array whose
// elements are size bytes each. Elements of one byte are counted as bytes
// are, and so are those of none, which only a struct or an array of no
// fields is, and which are bytes too.
func Elements(lo, hi *logic.Term, size int64) Span {
	if size <= 1 {
		return Bytes(lo, hi)
	}
	return Span{lo: lo, hi: hi, unit: size}
}

// Box returns the stretch of the one cell of a box of size bytes at at,
// for a pointer whose #arr is arr: a place at the byte at when arr is
// false, an element at the position at when it is true. Of a box of one
// byte the two are one location.
func Box(at, arr *logic.Term, size int64) Span {
	one := logic.Add(at, logic.IntLit(1))
	switch {
	case size <= 1 || arr.Op == logic.OpFalse:
		return Bytes(at, one)
	case arr.Op == logic.OpTrue:
		return Elements(at, one, size)
	}
	return Span{lo: at, hi: one, unit: size, arr: arr}
}

// Set reports whether s is a stretch.
func (s Span) Set() bool { return s.lo != nil }

// halves returns the stretches s is one of, each with the condition under
// which it is the one.
func (s Span) halves() ([]Span, []*logic.Term) {
	if s.arr == nil {
		return []Span{s}, []*logic.Term{logic.True()}
	}
	return []Span{Bytes(s.lo, s.hi), {lo: s.lo, hi: s.hi, unit: s.unit}}, []*logic.Term{logic.Not(s.arr), s.arr}
}

// In returns the positions [lo, hi) that the stretch holds in a region,
// and false when it holds none: a stretch of elements holds cells of its
// own elem region only, since an array holds nothing between its
// elements, and a stretch of bytes holds the cells of a region at bytes
// where they are and the elements of arrays at their floors.
func (s Span) In(r Region) (lo, hi *logic.Term, ok bool) {
	if s.lo == nil {
		panic("vego: internal error: the positions of no stretch")
	}
	size := max(r.Size, 1)
	if !r.Elem {
		size = 1
	}
	if s.arr != nil {
		// One cell, in the region its pointer points into.
		if r.Elem && size == s.unit {
			return s.lo, logic.Ite(s.arr, s.hi, s.lo), true
		}
		if !r.Elem {
			return s.lo, logic.Ite(s.arr, s.lo, s.hi), true
		}
		return nil, nil, false
	}
	switch {
	case s.unit == size && (r.Elem || s.unit == 1):
		return s.lo, s.hi, true
	case s.unit == 1:
		n := logic.IntLit(size)
		return logic.Div(s.lo, n), logic.Div(s.hi, n), true
	}
	return nil, nil, false
}

// Holds states that the position at of a cell of the region lies in the
// stretch.
func (s Span) Holds(r Region, at *logic.Term) *logic.Term {
	lo, hi, ok := s.In(r)
	if !ok {
		return logic.False()
	}
	return logic.And(logic.Le(lo, at), logic.Lt(at, hi))
}

// Outside states that the position at of a cell of the region lies
// outside the stretch.
func (s Span) Outside(r Region, at *logic.Term) *logic.Term {
	lo, hi, ok := s.In(r)
	if !ok {
		return logic.True()
	}
	return logic.Or(logic.Lt(at, lo), logic.Le(hi, at))
}

// Base returns the first position of the stretch in its own unit: for a
// stretch of bytes, the byte at which the value lies, from which its cells
// are counted, and the run of an array in it floored by the cell.
func (s Span) Base() *logic.Term {
	if s.lo == nil {
		panic("vego: internal error: the base of no stretch")
	}
	return s.lo
}

// Empty states that the stretch holds no position.
func (s Span) Empty() *logic.Term {
	return logic.Le(s.hi, s.lo)
}

// Apart states that two stretches of one allocation share no location.
// The elements of an array lie in a stretch of bytes exactly at its
// floored positions, so the two are compared in the unit of the elements;
// two stretches of elements of different sizes lie in different arrays.
func Apart(a, b Span) *logic.Term {
	return both(a, b, apart)
}

func apart(a, b Span) *logic.Term {
	if a.unit == 1 && b.unit > 1 {
		a, b = b, a
	}
	if a.unit != b.unit && b.unit != 1 {
		return logic.True()
	}
	lo, hi, _ := b.In(Region{Elem: a.unit > 1, Size: a.unit})
	return logic.Or(logic.Le(a.hi, lo), logic.Le(hi, a.lo))
}

// Inside states that the stretch a lies inside b, in one allocation. A
// value of bytes lies inside an array of larger elements only when it is
// empty.
func Inside(a, b Span) *logic.Term {
	return both(a, b, inside)
}

func inside(a, b Span) *logic.Term {
	if a.unit != b.unit && b.unit != 1 {
		return a.Empty()
	}
	lo, hi, _ := b.In(Region{Elem: a.unit > 1, Size: a.unit})
	return logic.And(logic.Le(lo, a.lo), logic.Le(a.hi, hi))
}

// A Byte is the byte address of a cell in its allocation, by which the
// rows of footprints and the reach of parameters count the cells they hold
// whatever region the cells lie in. The cell at the position p of an elem
// region of elements of n bytes is counted at p·n + n - 1, the last byte
// of the element at the index p of an array and a byte of the element at
// the floor p of a run in a struct, since that element begins in the n
// bytes from p·n; the stretch of bytes of a value holds it exactly when it
// holds the element, as a value never splits an element.
type Byte struct{ at *logic.Term }

// ByteOf returns the byte at which the rows count the cell at the position
// pos of a region.
func ByteOf(r Region, pos *logic.Term) Byte {
	if !r.Elem || r.Size <= 1 {
		return Byte{pos}
	}
	return Byte{logic.Add(logic.Mul(pos, logic.IntLit(r.Size)), logic.IntLit(r.Size-1))}
}

// AnyByte returns a byte address named by a variable that ranges over all
// of them, or by a byte that a row already counts.
func AnyByte(at *logic.Term) Byte { return Byte{at} }

// Term returns the number of the byte, to read a row at.
func (b Byte) Term() *logic.Term { return b.at }

// ByteBounds returns the bytes [lo, hi) that the stretch covers. Of a box
// it is the one byte at which its cell is counted, in the region its
// pointer points into.
func (s Span) ByteBounds() (lo, hi *logic.Term) {
	if s.lo == nil {
		panic("vego: internal error: the bytes of no stretch")
	}
	if s.unit == 1 {
		return s.lo, s.hi
	}
	n := logic.IntLit(s.unit)
	elo, ehi := logic.Mul(s.lo, n), logic.Mul(s.hi, n)
	if s.arr == nil {
		return elo, ehi
	}
	return logic.Ite(s.arr, elo, s.lo), logic.Ite(s.arr, ehi, s.hi)
}

// First returns the byte at which the rows count the first cell of the
// stretch.
func (s Span) First() Byte {
	if s.lo == nil {
		panic("vego: internal error: the first byte of no stretch")
	}
	elem := ByteOf(Region{Elem: true, Size: s.unit}, s.lo)
	if s.arr == nil {
		return elem
	}
	return Byte{logic.Ite(s.arr, elem.at, s.lo)}
}

// HoldsByte states that the stretch covers a byte.
func (s Span) HoldsByte(b Byte) *logic.Term {
	lo, hi := s.ByteBounds()
	return logic.And(logic.Le(lo, b.at), logic.Lt(b.at, hi))
}

// both applies a comparison to each pair of halves of two stretches, under
// the condition that they are the ones; two stretches of no box are
// compared once.
func both(a, b Span, compare func(a, b Span) *logic.Term) *logic.Term {
	if a.arr == nil && b.arr == nil {
		return compare(a, b)
	}
	as, aw := a.halves()
	bs, bw := b.halves()
	var cases []*logic.Term
	for i, x := range as {
		for j, y := range bs {
			cases = append(cases, logic.Implies(logic.And(aw[i], bw[j]), compare(x, y)))
		}
	}
	return logic.And(cases...)
}

// String spells the stretch for an error.
func (s Span) String() string {
	return fmt.Sprintf("[%v, %v) of %d", s.lo, s.hi, s.unit)
}
