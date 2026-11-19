package interfaces

import (
	"errors"
	"interfaceslib"
	"interfacesunread"
	"io"
)

// @Requires 0 <= qty <= 1000
// @Ensures True
func MayBeNil(p Pricer, qty int) (cents int) {
	cents, _ = p.Price("a", qty) // want `the interface value p may be nil`
	return cents
}

// @Requires p != nil
// @Ensures True
func OutOfRange(p Pricer, qty int) (cents int) {
	cents, _ = p.Price("a", qty) // want `precondition of p.Price may not hold: 0 <= qty <= 1000`
	return cents
}

// @Requires p != nil
// @Ensures cents <= 100
func TooMuch(p Pricer) (cents int) {
	cents, _ = p.Price("a", 1)
	return cents // want `postcondition may not hold: cents <= 100`
}

// @Requires s != nil And c != nil
// @Ensures True
func Unlisted(s Setter, c *Cell) {
	s.Set(c, 1) // want `s.Set may modify what it calls c.V, which Unlisted may not modify`
}

// @Requires s != nil And c != nil And 0 <= n <= 100
// @Modifies c.V
// @Ensures True
func Forgotten(s Setter, c *Cell, n int) {
	c.V = 5
	// @Invariant c.V = 5
	// @Invariant 0 <= i
	// @Variant n - i
	for i := 0; i < n; i++ { // want `loop invariant may not be preserved: c.V = 5`
		s.Set(c, i)
	}
}

// @Requires c != nil
// @Modifies c.V
// @Ensures True
func DeferredNil(s Setter, c *Cell) {
	defer s.Set(c, 3) // want `the interface value s may be nil`
}

type Plain interface {
	Get() (n int)
}

// @Requires p != nil
// @Ensures True
func NoContract(p Plain) (n int) {
	return p.Get() // want `cannot verify NoContract: p.Get calls Plain.Get, which has no contract`
}

// The shipped entry of Write says nothing of when it succeeds.
//
// @Requires w != nil
// @Ensures err = nil
func Foreign(w io.Writer, b []byte) (err error) {
	_, err = w.Write(b)
	return err // want `postcondition may not hold: err = nil`
}

type Response struct {
	Code int
	Body io.ReadCloser
}

// @Requires r != nil And r.Body != nil
// @Ensures True
func Close(r *Response) {
	defer r.Body.Close() // want `cannot verify Close: r.Body.Close calls Closer.Close, which has no contract`
}

// @Requires err != nil
// @Ensures True
func ErrorMethod(err error) (s string) {
	return err.Error() // want `cannot verify ErrorMethod: calling Error, a method of error, is not supported yet`
}

type Wrapper struct {
	Pricer
}

// @Requires w != nil And w.Pricer != nil
// @Ensures True
func Promoted(w *Wrapper) (cents int) {
	cents, _ = w.Price("a", 1) // want `cannot verify Promoted: Price is a method of an interface value that w holds in an embedded field`
	return cents
}

// @Requires p != nil
// @Ensures True
func Expression(p Pricer) (cents int) {
	cents, _ = Pricer.Price(p, "a", 1) // want `cannot verify Expression: a method expression, as in I.M\(x\), cannot be called yet`
	return cents
}

// Handler is given an error.
type Handler interface {
	// @Ensures True
	Handle(e error)
	// @Ensures True
	Take(x any)
}

// @Requires h != nil
// @Ensures True
func HandsError(h Handler, e error) {
	h.Handle(e) // want `cannot verify HandsError: e is passed to the method h.Handle and is an error whose origin is not known`
}

// @Requires h != nil
// @Ensures True
func HandsMade(h Handler) {
	h.Handle(errors.New("made"))
}

// @Requires h != nil
// @Ensures True
func HandsAny(h Handler, x any) {
	h.Take(x) // want `cannot verify HandsAny: x is passed to the method h.Take and is a value of type any, which can hold an error, or another interface`
}

// @Requires h != nil
// @Ensures True
func HandsPlain(h Handler, p Plain) {
	h.Take(p) // want `cannot verify HandsPlain: p is passed to the method h.Take and is a value of type any`
}

// @Requires v != nil
// @Ensures True
func HandsHalfContracted(v Visitor, p Plain) {
	_ = p
}

// A literal used as a value cannot call through an interface value.
//
// @Requires p != nil
// @Ensures f != nil
func Priced(p Pricer) (f Mapper) {
	return func(x int) (y int) {
		_, _ = p.Price("a", 1) // want `cannot verify Priced: the function literal used as a value calls through the interface value p`
		return x
	}
}

// Mapper maps a number.
//
// @Requires 0 <= x <= 1000
// @Ensures 0 <= y <= 1000
type Mapper func(x int) (y int)

// @Requires c != nil
// @Ensures True
func Unread(c interfacesunread.Counter) (n int) {
	return c.Count() // want `the contract of Counter.Count cannot be used: the annotations of package interfacesunread were not all read` `cannot verify Unread: the contract of Counter.Count could not be understood`
}

// @Requires s != nil
// @Ensures n <= 50
func LibBound(s interfaceslib.Sizer) (n int) {
	return s.Size() // want `postcondition may not hold: n <= 50`
}
