package typederrors

import (
	"errors"
	"fmt"
)

// errors.As and errors.AsType (S5 of F33).

// @Ensures line = n
func AsLine(n int) (line int) {
	var pe *PE
	if errors.As(Placed(n), &pe) {
		return pe.Line
	}
	return 0
}

// @Ensures line = n
func AsWrapped(n int) (line int) {
	err := Placed(n)
	if err != nil {
		err = fmt.Errorf("at: %w", err)
	}
	var pe *PE
	if errors.As(err, &pe) {
		return pe.Line
	}
	return 0
}

// @Ensures line = n
func AsTypeLine(n int) (line int) {
	if pe, ok := errors.AsType[*PE](Placed(n)); ok {
		return pe.Line
	}
	return 0
}

// @Ensures ~r
func AsOtherType(n int) (r bool) {
	var e Error
	return errors.As(Placed(n), &e)
}

// @Ensures ~r
func AsMade() (r bool) {
	var pe *PE
	return errors.As(errors.New("x"), &pe)
}

// @Ensures r <-> n < 0
func AsCode(n int) (r bool) {
	err := Parse(n)
	if err != nil {
		err = fmt.Errorf("code: %w", err)
	}
	var e Error
	return errors.As(err, &e) && e == ErrSyntax
}

// @Ensures err = nil <-> n = 0
// @Ensures n != 0 -> as(err, *PE)
func SaysAs(n int) (err error) {
	if err := Placed(n); err != nil {
		return fmt.Errorf("says: %w", err)
	}
	return nil
}

// @Ensures r <-> n != 0
func ReadsSaysAs(n int) (r bool) {
	var pe *PE
	return errors.As(SaysAs(n), &pe)
}

// IsErr is an error with an Is method on its pointer receiver, which an
// error that holds an IsErr value does not have.
type IsErr struct{ n int }

// @Ensures True
func (e IsErr) Error() (s string) { return "is" }

// @Ensures True
func (e *IsErr) Is(target error) (r bool) { return true }

// @Ensures ~r
func ValueHasNoIs() (r bool) {
	return errors.Is(IsErr{1}, ErrSyntax)
}

// @Ensures ~r
func ValueAsOther() (r bool) {
	var e Error
	return errors.As(IsErr{1}, &e)
}

// @Ensures False
func AsNotFalse(n int) (r bool) {
	var pe *PE
	return errors.As(Placed(n), &pe) // want `postcondition may not hold: False`
}

// @Ensures True
func AsPanics(err error) (r bool) {
	var x int
	return errors.As(err, &x) // want `errors.As panics here: the target has type int, which is not an interface and does not implement error`
}

// @Ensures True
func AsInterface(err error) (r bool) {
	var x interface{ Timeout() bool }
	return errors.As(err, &x) // want `errors.As with a target of the interface type interface\{Timeout\(\) bool\} is not supported yet`
}

// @Ensures True
func AsUnknown(err error) (r bool) {
	var pe *PE
	return errors.As(err, &pe) // want `errors.As would run the As and Unwrap methods of err, an error whose origin is not known`
}

// @Ensures True
func AsField(err error) (r bool) {
	var h struct{ p *PE }
	return errors.As(Placed(1), &h.p) // want `errors.As is supported only as errors.As\(err, &v\) for a local variable v`
}

// @Ensures True
func AsLocked() (r bool) {
	var l Locked
	return errors.As(Placed(1), &l) // want `errors.As copies the value it finds, a value of type Locked, which holds a sync.Mutex`
}

// Wrap embeds a *PE, whose Error it promotes: verified code cannot convert
// it, but an error from elsewhere may hold one (typederrorsclient).
type Wrap struct{ *PE }

// AsKeepsTarget keeps its target when errors.As finds nothing.
//
// @Ensures line = 5
func AsKeepsTarget() (line int) {
	pe := &PE{Line: 5}
	var err error
	errors.As(err, &pe)
	return pe.Line
}
