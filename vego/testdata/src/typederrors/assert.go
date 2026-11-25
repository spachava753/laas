package typederrors

import "errors"

// Type assertions and type switches on errors (S3 of F33).

// @Ensures err = nil <-> n = 0
// @Ensures n != 0 -> holds(err, *PE) And err.(*PE) != nil And err.(*PE).Line = n
func Placed(n int) (err error) {
	if n != 0 {
		return &PE{Line: n}
	}
	return nil
}

// @Ensures line = n
func LineOf(n int) (line int) {
	if pe, ok := Placed(n).(*PE); ok {
		return pe.Line
	}
	return 0
}

// @Requires n != 0
// @Ensures line = n
func MustLineOf(n int) (line int) {
	return Placed(n).(*PE).Line
}

// @Ensures True
func MayPanic(n int) (line int) {
	return Placed(n).(*PE).Line // want `the type assertion Placed\(n\).\(\*PE\) may panic: Placed\(n\) may not hold a \*PE; use the form v, ok := Placed\(n\).\(\*PE\), or show that it holds one, as a contract does with holds\(err, T\)`
}

// @Ensures ~r
func NotAnError(n int) (r bool) {
	_, r = Placed(n).(Error)
	return r
}

// @Ensures r <-> n != 0
func AsError(n int) (r bool) {
	_, r = Placed(n).(error)
	return r
}

// @Ensures k = 0 <-> n = 0
// @Ensures n < 0 -> k = 2
// @Ensures n > 0 -> k = 1
func Kind(n int) (k int) {
	var err error
	if n < 0 {
		err = ErrSyntax
	} else if n > 0 {
		err = errors.New("x")
	}
	switch e := err.(type) {
	case nil:
		return 0
	case Error:
		if e == ErrSyntax {
			return 2
		}
		return 3
	case *PE, SErr:
		return 4
	default:
		return 1
	}
}

// @Ensures k = 0 <-> n = 0
func KindWithin(n int) (k int) {
	switch e := Placed(n).(type) {
	case *PE:
		if e == nil {
			return -1
		}
		return e.Line
	}
	return 0
}

// @Ensures False
func NotFalse(n int) (r bool) {
	_, ok := Placed(n).(Error)
	return ok // want `postcondition may not hold: False`
}

// @Ensures r = 0
func SwitchMayMiss(n int) (r int) {
	switch err := Placed(n).(type) {
	case *PE:
		return err.Line // want `postcondition may not hold: r = 0`
	}
	return 0
}


// HeldLine reads what its parameter holds, which its Requires says is a
// pointer that is not nil.
//
// @Requires holds(err, *PE) And err.(*PE) != nil
// @Ensures line = err.(*PE).Line
func HeldLine(err error) (line int) {
	return err.(*PE).Line
}

// ZeroWhenNot reads the value of the two-result form when the error holds
// no *PE, which is the zero value.
//
// @Ensures n = 0 -> r
func ZeroWhenNot(n int) (r bool) {
	pe, _ := Placed(n).(*PE)
	return pe == nil
}

// @Ensures ~r
func MadeNotTyped() (r bool) {
	_, r = errors.New("x").(Error)
	return r
}
