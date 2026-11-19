// Package interfaces holds programs with values of interface types other
// than error: held, passed, stored, returned, compared with nil, and
// converted, and the forms that are refused.
package interfaces

import (
	"errors"
	"io"
)

type Shape interface {
	// @Ensures a >= 0
	Area() (a int)
}

type Named interface {
	Shape
	Name() (n string)
}

// @Ensures same = (s = nil)
func IsNil(s Shape) (same bool) {
	return s == nil
}

// @Ensures t = nil <-> s = nil
func Pass(s Shape) (t Shape) {
	return s
}

type Holder struct {
	Count int
	Shape Shape
	Body  io.ReadCloser
}

// @Requires h != nil
// @Modifies h
// @Ensures h.Shape' = nil <-> s = nil
// @Ensures h.Count' = h.Count + 0
func Store(h *Holder, s Shape) {
	h.Shape = s
}

// @Requires h != nil
// @Ensures s = nil <-> h.Shape = nil
func Load(h *Holder) (s Shape) {
	return h.Shape
}

// A struct with a field of interface type can be copied and its other
// fields read, as before interfaces were modelled.
//
// @Requires h != nil
// @Modifies h
// @Ensures h.Count' = g.Count
func Copy(h *Holder, g Holder) {
	*h = g
}

// @Ensures |shapes| = 2
// @Ensures shapes[0] = nil
// @Ensures shapes[1] = nil <-> s = nil
func Slice(s Shape) (shapes []Shape) {
	shapes = []Shape{nil, s}
	if s == nil {
		shapes[1] = Shape(Named(nil))
		return []Shape{nil, Pass(s)}
	}
	return shapes
}

// @Ensures m != nil
func Keyed(s Shape) (m map[string]Shape) {
	m = map[string]Shape{"a": s}
	m["b"] = nil
	return m
}

// An interface value converted to an interface whose methods it has keeps
// what it is: the nil interface stays nil.
//
// @Ensures (s = nil) <-> (t = nil)
// @Ensures (s = nil) <-> (a = nil)
func Smaller(n Named) (s Shape, t Shape, a any) {
	s = n
	t = Shape(n)
	a = n
	if s != nil {
		_ = s
	}
	return s, t, a
}

// @Ensures a = nil
func FromNil() (a any) {
	var n Named
	a = n
	return a
}

// @Ensures a != nil
func Anything(x int, p *Holder, s []int) (a any) {
	a = x
	a = p
	a = s
	a = (*Holder)(nil)
	return a
}

// @Ensures (a = nil) <-> (err = nil)
func ErrorInAny(err error) (a any) {
	return err
}

// @Ensures a != nil
func MadeErrorInAny() (a any) {
	return errors.New("x")
}

// @Ensures a = nil
func NilErrorInAny() (a any) {
	var err error
	return err
}

// @Ensures True
func Switch(s Shape) (n int) {
	switch s {
	case nil:
		return 0
	}
	return 1
}

var errNoShape = errors.New("no shape")
