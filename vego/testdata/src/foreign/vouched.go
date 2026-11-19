package foreign

import (
	"errors"
	"fmt"

	"foreignlib"
)

// The entry of Next vouches for its errors, so they can be wrapped and
// searched.
//
// @Requires s != nil
// @Ensures err != nil -> is(err, foreignlib.ErrFull)
func Wraps(s foreignlib.Source) (n int, err error) {
	n, err = s.Next()
	if err != nil {
		return 0, fmt.Errorf("next: %w", err)
	}
	return n, nil
}

// @Requires s != nil
// @Ensures full -> err != nil
func Full(s foreignlib.Source) (full bool, err error) {
	_, err = s.Next()
	return errors.Is(err, foreignlib.ErrFull), err
}

// @Requires d != nil
// @Ensures True
func WrapsDone(d foreignlib.Done) (err error) {
	if err := d(); err != nil {
		return fmt.Errorf("done: %w", err)
	}
	return nil
}

// The entry of Put does not vouch.
//
// @Requires s != nil
// @Ensures True
func WrapsPut(s foreignlib.Sink) (err error) {
	if _, err := s.Put(1); err != nil {
		return fmt.Errorf("put: %w", err) // want `cannot verify WrapsPut: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// Counted is a source of this package whose errors are known.
type Counted struct{}

// @Ensures err = nil
func (Counted) Next() (n int, err error) {
	return 1, nil
}

// @Ensures s != nil
func NewCounted() (s foreignlib.Source) {
	return Counted{}
}

// Stale returns an error it holds, whose origin is not known.
type Stale struct {
	err error
}

// @Requires s.err = nil Or s.err = foreignlib.ErrFull
// @Ensures err = s.err
func (s Stale) Next() (n int, err error) {
	return 0, s.err
}

// @Requires st.err = nil Or st.err = foreignlib.ErrFull
// @Ensures s != nil
func NewStale(st Stale) (s foreignlib.Source) {
	return st // want `Next may return an error whose origin is not known in err, and the trusted contract of \(foreignlib.Source\).Next vouches for the errors there; return only errors made by errors.New or fmt.Errorf, or vouched for, in Stale.Next used as a method of foreignlib.Source at vouched.go:\d+:\d+`
}

// @Ensures d != nil
func DoneRight() (d foreignlib.Done) {
	return func() error { return foreignlib.ErrFull }
}

// @Requires e = nil Or e = foreignlib.ErrFull
// @Ensures d != nil
func DoneWith(e error) (d foreignlib.Done) {
	return func() error { return e } // want `the function literal may return an error whose origin is not known in err, and the trusted contract of foreignlib.Done vouches for the errors there`
}

// @Requires o != nil
// @Ensures True
func Opens(o foreignlib.Opener) (s foreignlib.Sink) {
	return o.Open() // want `the trusted contract of \(foreignlib.Opener\).Open \(trusted.yaml:\d+\) cannot be used: its vouches lists s, whose type foreignlib.Sink is not error` `cannot verify Opens: the contract of Opener.Open could not be understood`
}

// Holder holds a sink.
type Holder struct {
	S foreignlib.Sink
}

func refill(h *Holder)          {}
func refillUnclaimed(h *Holder) {}
func vouchesNothing(b *Box)     {}

// A trusted function that writes a sink vouches for it under the parameter
// whose memory it writes.
//
// @Requires h != nil
// @Modifies h
// @Ensures err = nil -> 0 <= y <= 2
func Refills(h *Holder) (y int, err error) {
	refill(h)
	if h.S == nil {
		return 0, nil
	}
	return h.S.Put(1)
}

// @Requires h != nil
// @Modifies h
// @Ensures True
func RefillsUnclaimed(h *Holder) {
	refillUnclaimed(h) // want `the trusted contract of foreign.refillUnclaimed \(trusted.yaml:\d+\) cannot be used: its modifies "h" covers memory that can hold a function value or an interface value of a type with a contract; list h under vouches` `cannot verify RefillsUnclaimed: refillUnclaimed has a contract that could not be understood`
}

// @Requires b != nil
// @Modifies b
// @Ensures True
func VouchesNothing(b *Box) {
	vouchesNothing(b) // want `the trusted contract of foreign.vouchesNothing \(trusted.yaml:\d+\) cannot be used: its vouches lists b, but nothing its modifies lists under b can hold` `cannot verify VouchesNothing: vouchesNothing has a contract that could not be understood`
}

// A variable of a vouching type bound to a literal used in place runs the
// literal where it is called: the entry plays no part, and the error the
// literal returns is e, whose origin is not known.
//
// @Requires e != nil
// @Ensures True
func BoundDone(e error) (err error) {
	var d foreignlib.Done = func() error { return e }
	if err := d(); err != nil {
		return fmt.Errorf("done: %w", err) // want `cannot verify BoundDone: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// MakesErr makes an error.
//
// @Ensures err != nil
type MakesErr func() (err error)

// errors.New calls nothing, so a value may call it. Before, it counted as
// a function that may call through a value, and this was refused.
//
// @Ensures m != nil
func MakesNew() (m MakesErr) {
	return func() error { return errors.New("made") }
}

// fmt.Errorf formats its operands, which can run their methods.
//
// @Ensures m != nil
func MakesWrapped() (m MakesErr) {
	return func() error {
		return fmt.Errorf("made: %w", foreignlib.ErrFull) // want `cannot verify MakesWrapped: the function literal used as a value calls Errorf, which may call through a function value or an interface value: Errorf formats its operands, which can run their methods`
	}
}
