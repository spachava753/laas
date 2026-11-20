// Package originpath reuses one error variable for calls whose errors a
// contract vouches for and calls whose errors nothing vouches for. Where an
// error is used, only the assignments on the paths that reach the use
// decide its origin.
package originpath

import (
	"errors"
	"fmt"
)

var (
	errA      = errors.New("a")
	ErrFailed = errors.New("failed")
)

func vouched() (err error)   { return nil }
func unvouched() (err error) { return nil }
func closeIt() (err error)   { return nil }
func log(e error)            {}

// Opens wraps the error of a vouched call before the variable is reused for
// a call whose errors nothing vouches for.
//
// @Ensures True
func Opens() (err error) {
	err = vouched()
	if err != nil {
		return fmt.Errorf("open: %w", err)
	}
	err = unvouched()
	return err
}

// BothBranches assigns an error of known origin on both branches.
//
// @Ensures err = nil <-> fine
func BothBranches(c, fine bool) (err error) {
	if fine {
		return nil
	}
	if c {
		err = vouched()
	} else {
		err = errA
	}
	return fmt.Errorf("both: %w", err)
}

// Switched assigns an error of known origin in every case.
//
// @Ensures True
func Switched(n int) (err error) {
	switch n {
	case 0:
		err = vouched()
	case 1:
		err = errA
	default:
		err = unvouched()
		err = nil
	}
	if err != nil {
		return fmt.Errorf("switched: %w", err)
	}
	return nil
}

// Looped wraps, at the top of each iteration, what the last one assigned.
//
// @Requires 0 <= n
// @Ensures True
func Looped(n int) (err error) {
	// @Variant n - i
	for i := 0; i < n; i++ {
		if err != nil {
			return fmt.Errorf("looped: %w", err)
		}
		if i == 3 {
			continue
		}
		if i == 5 {
			break
		}
		err = vouched()
	}
	return err
}

// Shadowed declares a new err in an if; the outer one is not used there.
//
// @Ensures True
func Shadowed() (err error) {
	err = unvouched()
	if err := vouched(); err != nil {
		return fmt.Errorf("shadowed: %w", err)
	}
	return err
}

// Rewrapped uses err and assigns it in the same statement.
//
// @Ensures True
func Rewrapped() (err error) {
	err = vouched()
	if err != nil {
		err = fmt.Errorf("first: %w", err)
		return fmt.Errorf("second: %w", err)
	}
	return nil
}

// Reassigned formats a parameter after assigning it an error of its own.
//
// @Ensures err = nil <-> fine
func Reassigned(e error, fine bool) (err error) {
	if fine {
		return nil
	}
	e = errA
	return fmt.Errorf("reassigned: %w", e)
}

// LiteralReassigns gives a literal an error of unknown origin, which the
// literal replaces before it formats it.
//
// @Ensures err = nil <-> fine
func LiteralReassigns(fine bool) (err error) {
	if fine {
		return nil
	}
	wrap := func(x error) error {
		x = errA
		return fmt.Errorf("wrap: %w", x)
	}
	return wrap(unvouched())
}

// Normalised returns only errors of known origin: its bare return comes
// after err is assigned a vouched error.
//
// @Ensures True
func Normalised() (err error) {
	err = unvouched()
	if err != nil {
		return ErrFailed
	}
	err = vouched()
	return
}

// Load wraps the error of a vouched call and returns a sentinel for the
// error of the other, so every return returns an error of known origin.
//
// @Ensures True
func Load() (err error) {
	err = vouched()
	if err != nil {
		return fmt.Errorf("load: %w", err)
	}
	err = unvouched()
	if err != nil {
		return ErrFailed
	}
	return nil
}

// Closes keeps the error of closeIt in a deferred literal, which runs only
// after the return.
//
// @Ensures True
func Closes() (err error) {
	err = vouched()
	if err != nil {
		return fmt.Errorf("open: %w", err)
	}
	defer func() {
		if cerr := closeIt(); err == nil {
			err = cerr
		}
	}()
	err = unvouched()
	return err
}

// DeferKnownThenUnknown hands log the error at the defer statement, where
// it has a known origin.
//
// @Ensures True
func DeferKnownThenUnknown() (err error) {
	err = errA
	defer log(err)
	err = unvouched()
	return err
}

// Posted assigns err in the post statement of a loop, which reaches the
// condition and the next iteration.
//
// @Requires 0 <= n
// @Ensures True
func Posted(n int) (err error) {
	// @Variant n - i
	for i := 0; i < n; i, err = i+1, vouched() {
		if err != nil {
			return fmt.Errorf("posted: %w", err)
		}
	}
	return nil
}

// Fetch is a function type whose values vouch for their errors.
//
// @Ensures True
// @Vouches err
type Fetch func() (err error)

// MakeFetch makes a Fetch that reuses err and returns only errors of known
// origin.
//
// @Ensures f != nil
func MakeFetch() (f Fetch) {
	return func() (err error) {
		err = vouched()
		if err != nil {
			return fmt.Errorf("fetch: %w", err)
		}
		err = unvouched()
		if err != nil {
			return ErrFailed
		}
		return nil
	}
}

// VarInLoop declares err in each iteration, which forgets what the last
// iteration assigned it.
//
// @Requires 0 <= n
// @Ensures True
func VarInLoop(n int, c bool) (result error) {
	// @Variant n - i
	for i := 0; i < n; i++ {
		var err error
		if c {
			err = vouched()
		}
		if err != nil {
			return fmt.Errorf("var: %w", err)
		}
		err = unvouched()
		if err != nil {
			return err
		}
	}
	return nil
}

// CallsLater wraps the error of a function declared after it, which returns
// only errors it made.
//
// @Ensures err = nil <-> c
func CallsLater(c bool) (err error) {
	err = later(c)
	if err != nil {
		return fmt.Errorf("calls later: %w", err)
	}
	return nil
}

// Passes returns the error of a function declared after it, so it returns
// only errors of known origin once that function does.
//
// @Ensures err = nil <-> c
func Passes(c bool) (err error) {
	err = later(c)
	return err
}

// @Ensures err = nil <-> c
func later(c bool) (err error) {
	if c {
		return nil
	}
	return errors.New("later")
}
