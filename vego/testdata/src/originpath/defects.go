package originpath

import (
	"errors"
	"fmt"
)

// LoopBack wraps, at the top of an iteration, what the last one assigned,
// which a call whose errors nothing vouches for may have.
//
// @Requires 0 <= n
// @Ensures True
func LoopBack(n int) (err error) {
	// @Variant n - i
	for i := 0; i < n; i++ {
		if err != nil {
			return fmt.Errorf("looped: %w", err) // want `formatting err would run the methods of an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, can be formatted; err may hold here the error assigned unvouched\(\) at defects.go:19:9, a call whose errors nothing vouches for, in an earlier iteration of the loop; declare err inside the loop, or give that error a variable of its own`
		}
		err = unvouched()
	}
	return err
}

// OneBranch assigns an error of unknown origin on one branch only.
//
// @Ensures True
func OneBranch(c bool) (err error) {
	err = errA
	if c {
		err = unvouched()
	}
	if err != nil {
		return fmt.Errorf("one: %w", err) // want `err may hold here the error assigned unvouched\(\) at defects.go:30:9, a call whose errors nothing vouches for, on a path that reaches this use; give that error a variable of its own`
	}
	return nil
}

// OneCase assigns an error of unknown origin in one case.
//
// @Ensures True
func OneCase(n int) (err error) {
	switch n {
	case 0:
		err = vouched()
	case 1:
		err = unvouched()
	}
	if err != nil {
		return fmt.Errorf("case: %w", err) // want `err may hold here the error assigned unvouched\(\) at defects.go:46:9, a call whose errors nothing vouches for, on a path that reaches this use; give that error a variable of its own`
	}
	return nil
}

// AfterLoop wraps after a loop whose body may assign an error of unknown
// origin.
//
// @Requires 0 <= n
// @Ensures True
func AfterLoop(n int) (err error) {
	err = errA
	// @Variant n - i
	for i := 0; i < n; i++ {
		err = unvouched()
	}
	if err != nil {
		return fmt.Errorf("after: %w", err) // want `err may hold here the error assigned unvouched\(\) at defects.go:63:9, a call whose errors nothing vouches for, on a path that reaches this use; give that error a variable of its own`
	}
	return nil
}

// HalfAssigned formats a parameter that one path leaves as it was given.
//
// @Ensures True
func HalfAssigned(e error, c bool) (err error) {
	if c {
		e = errA
	}
	if e != nil {
		return fmt.Errorf("half: %w", e) // want `e is a parameter, and on a path to here nothing assigns it, so it may still hold the error it was passed, which can be returned unchanged but not formatted`
	}
	return nil
}

// SameStatement wraps the error of unvouched in the statement that assigns
// the wrapping to err.
//
// @Ensures True
func SameStatement() (err error) {
	err = unvouched()
	if err != nil {
		err = fmt.Errorf("first: %w", err) // want `err is assigned unvouched\(\) at defects.go:89:8, a call whose errors nothing vouches for`
	}
	return err
}

// Chained moves an error of unknown origin into err through a second
// variable in a loop.
//
// @Requires 0 <= n
// @Ensures True
func Chained(n int) (err error) {
	err = errors.New("a")
	e2 := errors.New("b")
	// @Variant n - i
	for i := 0; i < n; i++ {
		err = e2
		e2 = unvouched()
	}
	if err != nil {
		return fmt.Errorf("chained: %w", err) // want `err may hold here the error assigned e2 at defects.go:106:9, an error whose origin is not known, on a path that reaches this use`
	}
	return nil
}

// DeferUnknown hands log the error at the defer statement, where nothing
// vouches for it.
//
// @Ensures True
func DeferUnknown() (err error) {
	err = unvouched()
	defer log(err) // want `err is passed to log, which is trusted, and is an error whose origin is not known; err is assigned unvouched\(\) at defects.go:120:8, a call whose errors nothing vouches for`
	err = nil
	return err
}

// PostedUnknown assigns an error of unknown origin in a post statement.
//
// @Requires 0 <= n
// @Ensures True
func PostedUnknown(n int) (err error) {
	// @Variant n - i
	for i := 0; i < n; i, err = i+1, unvouched() {
		if err != nil {
			return fmt.Errorf("posted: %w", err) // want `err may hold here the error assigned unvouched\(\) at defects.go:132:35, a call whose errors nothing vouches for, in an earlier iteration of the loop`
		}
	}
	return nil
}

// ReadLater reads, in a deferred literal, a variable that is assigned an
// error of unknown origin after the defer statement.
//
// @Ensures True
func ReadLater() (err error) {
	e := vouched()
	defer func() {
		log(e) // want `e is passed to log, which is trusted, and is an error whose origin is not known; the function literal at defects.go:146:8 reads e and may run after any assignment to it, and e is assigned unvouched\(\) at defects.go:149:6, a call whose errors nothing vouches for; give that error a variable of its own`
	}()
	e = unvouched()
	return nil
}

// ReadBetween calls a literal that reads err between two assignments.
//
// @Ensures True
func ReadBetween() (err error) {
	e := vouched()
	func() {
		log(e) // want `the function literal at defects.go:158:2 reads e and may run after any assignment to it, and e is assigned unvouched\(\) at defects.go:161:6`
	}()
	e = unvouched()
	return nil
}

// AssignedInLiteral formats a variable that a literal it calls later
// assigns.
//
// @Ensures True
func AssignedInLiteral() (err error) {
	e := vouched()
	reset := func() { e = unvouched() }
	if e != nil {
		return fmt.Errorf("assigned: %w", e) // want `e is assigned in the function literal at defects.go:171:11, which may run at any point, so every assignment to e counts, and e is assigned unvouched\(\) at defects.go:171:24, a call whose errors nothing vouches for; give that error a variable of its own`
	}
	reset()
	return nil
}

// ClosesBound defers a literal bound to a variable, which it also calls
// before it formats err.
//
// @Ensures True
func ClosesBound() (err error) {
	err = vouched()
	keep := func() {
		if cerr := closeIt(); err == nil {
			err = cerr
		}
	}
	defer keep()
	keep()
	if err != nil {
		return fmt.Errorf("open: %w", err) // want `err is assigned in the function literal at defects.go:185:10, which may run at any point, so every assignment to err counts, and err is assigned cerr at defects.go:187:10, an error whose origin is not known; give that error a variable of its own`
	}
	return nil
}

// TypeSwitched returns the variable of a type switch, which holds what it
// was given.
//
// @Ensures True
func TypeSwitched(e error) (err error) {
	switch x := e.(type) { // want `type switches are not supported`
	case error:
		return x
	}
	return nil
}

// LiteralGiven gives a literal an error of unknown origin, which it formats.
//
// @Ensures True
func LiteralGiven(c bool) (err error) {
	wrap := func(x error) error {
		if c {
			x = errA
		}
		return fmt.Errorf("wrap: %w", x) // want `x is a parameter of the function literal, and is given unvouched\(\) at defects.go:220:14, a call whose errors nothing vouches for`
	}
	return wrap(unvouched())
}

// CachedCycle moves errors between two variables in a loop, one of which
// a branch assigns an error of unknown origin. Deciding what it publishes
// asks first about err at the return, through e2 = err while err = e2 is
// still being decided.
//
// @Requires 0 <= n
// @Ensures True
func CachedCycle(n int, c bool) (err error) {
	err = errA
	e2 := errors.New("b")
	// @Variant n - i
	for i := 0; i < n; i++ {
		if i == 7 {
			return err
		}
		err = e2
		e2 = err
		log(e2) // want `e2 is assigned err at defects.go:239:8, an error whose origin is not known`
		if c {
			e2 = unvouched()
		}
	}
	return nil
}
