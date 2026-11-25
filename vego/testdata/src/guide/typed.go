package guide

import (
	"errors"
	"fmt"
)

// The programs of "Errors of your own types" in the guide (F33).

// SyntaxError is an error of a type of its own.
type SyntaxError int

// @Ensures True
func (e SyntaxError) Error() (s string) { return "syntax error" }

const (
	ErrBadDigit SyntaxError = 1
	ErrTooLong  SyntaxError = 2
)

// ParseDigit returns the value of a decimal digit.
//
// @Ensures err = nil <-> 48 <= c <= 57
// @Ensures err = nil -> d = c - 48
// @Ensures err != nil -> err = ErrBadDigit
func ParseDigit(c byte) (d int, err error) {
	if c < '0' || c > '9' {
		return 0, ErrBadDigit
	}
	return int(c - '0'), nil
}

// IsBadDigit compares the error with the constant.
//
// @Ensures bad <-> ~(48 <= c <= 57)
func IsBadDigit(c byte) (bad bool) {
	_, err := ParseDigit(c)
	return err == ErrBadDigit
}

// ByteError says which byte was wrong.
type ByteError byte

// @Ensures True
func (e ByteError) Error() (s string) { return "bad byte" }

// CheckBytes reports the first byte that is not a lowercase letter.
//
// @Ensures err = nil <-> (Forall k in [0, |s|) : 97 <= s[k] <= 122)
// @Ensures err != nil -> (Exists k in [0, |s|) : err = ByteError(s[k]))
func CheckBytes(s []byte) (err error) {
	// @Invariant 0 <= i <= |s|
	// @Invariant Forall k in [0, i) : 97 <= s[k] <= 122
	// @Variant |s| - i
	for i := 0; i < len(s); i++ {
		if s[i] < 'a' || s[i] > 'z' {
			return ByteError(s[i])
		}
	}
	return nil
}

// LineError is an error that a pointer holds.
type LineError struct{ Line int }

// @Ensures True
func (e *LineError) Error() (s string) { return "error at a line" }

// ParseLine fails at a line it names.
//
// @Ensures err = nil <-> n <= 0
// @Ensures err != nil -> holds(err, *LineError) And err.(*LineError) != nil And err.(*LineError).Line = n
func ParseLine(n int) (err error) {
	if n > 0 {
		return &LineError{Line: n}
	}
	return nil
}

// FailingLine takes the line out of the error.
//
// @Ensures line = n Or (n <= 0 And line = 0)
func FailingLine(n int) (line int) {
	if le, ok := ParseLine(n).(*LineError); ok {
		return le.Line
	}
	return 0
}

// MustLine asserts that the error holds a *LineError.
//
// @Ensures True
func MustLine(n int) (line int) {
	return ParseLine(n).(*LineError).Line // want `vego: the type assertion ParseLine\(n\).\(\*LineError\) may panic: ParseLine\(n\) may not hold a \*LineError; use the form v, ok := ParseLine\(n\).\(\*LineError\), or show that it holds one, as a contract does with holds\(err, T\)`
}

// Describe tells the errors apart.
//
// @Ensures k = 0 <-> n = 0
func Describe(n int) (k int) {
	var err error
	if n < 0 {
		err = ErrTooLong
	} else if n > 0 {
		err = ParseLine(n)
	}
	switch e := err.(type) {
	case nil:
		return 0
	case SyntaxError:
		if e == ErrTooLong {
			return 1
		}
		return 2
	case *LineError:
		return 3
	default:
		return 4
	}
}

// LoadLine wraps the error of ParseLine.
//
// @Ensures err = nil <-> n <= 0
// @Ensures n > 0 -> as(err, *LineError)
func LoadLine(n int) (err error) {
	if err := ParseLine(n); err != nil {
		return fmt.Errorf("load: %w", err)
	}
	return nil
}

// LineOf finds the *LineError inside what LoadLine returns.
//
// @Ensures n > 0 -> found
func LineOf(n int) (found bool) {
	var le *LineError
	return errors.As(LoadLine(n), &le)
}

// LineOfType asks errors.AsType of what ParseLine returns.
//
// @Ensures found <-> n > 0
func LineOfType(n int) (found bool) {
	_, found = errors.AsType[*LineError](ParseLine(n))
	return found
}

// TargetNotError hands errors.As a target that is not an error.
//
// @Ensures True
func TargetNotError(n int) (found bool) {
	var line int
	return errors.As(LoadLine(n), &line) // want `vego: cannot verify TargetNotError: errors.As panics here: the target has type int, which is not an interface and does not implement error`
}

// WithCause has an Unwrap method, so its errors have no known origin.
type WithCause struct{ code int }

// @Ensures True
func (w WithCause) Error() (s string) { return "with cause" }

// @Ensures e = nil
func (w WithCause) Unwrap() (e error) { return nil }

// ReportCause formats an error of a type without a known origin.
//
// @Ensures err != nil
func ReportCause() (err error) {
	var cause error = WithCause{code: 1}
	return fmt.Errorf("report: %w", cause) // want `vego: cannot verify ReportCause: formatting cause would run the methods of an error whose origin is not known; .*cause is assigned WithCause\{…\} at typed.go:\d+:\d+, a value of type WithCause, whose errors have no known origin: WithCause has a method Unwrap, which errors.Is, errors.As, or fmt would run`
}

// NonNeg maps an integer to one that is not negative.
//
// @Ensures y >= 0
type NonNeg func(x int) (y int)

type HookError struct{ Fix NonNeg }

// @Ensures True
func (e *HookError) Error() (s string) { return "hook failed" }

// @Ensures r >= 0
func Repair(err error) (r int) {
	if he, ok := err.(*HookError); ok && he != nil && he.Fix != nil { // want `cannot verify Repair: asserting an error to \*HookError is not supported: it holds in field Fix a function value of type NonNeg, which has a contract, and nothing claims that a value taken out of an interface value meets that contract: code that is not verified may have made it`
		return he.Fix(0)
	}
	return 0
}
