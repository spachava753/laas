package values

// The exception for success that hangs on the outside, through a function
// literal whose body ends in several ways: what decides which end is
// reached decides what comes after.

type flag struct{ bad bool }

type held struct{ k int }

func outsideNumber() int { return 0 }

// ExcusedThroughLiteral fails when a call inside a literal with two ends
// fails, which nothing predicts.
//
// @Ensures True
func ExcusedThroughLiteral() (err error) {
	fl := &flag{}
	func() {
		if e := external(); e != nil {
			fl.bad = true
		}
	}()
	if fl.bad {
		return errOutOfRange
	}
	return nil
}

// ExcusedThroughResult fails when the result of a literal, decided by a
// call nothing predicts, says so.
//
// @Ensures True
func ExcusedThroughResult() (err error) {
	bad := func() bool {
		if outsideNumber() > 0 {
			return true
		}
		return false
	}()
	if bad {
		return errOutOfRange
	}
	return nil
}

// NotExcusedThroughLiteral calls something nothing predicts inside a
// literal with two ends, but fails because of its input alone.
//
// @Ensures True
func NotExcusedThroughLiteral(n int) (err error) { // want `the contract of NotExcusedThroughLiteral may also be met by a function that always returns an error`
	fl := &flag{}
	func() {
		_ = outsideNumber()
		if n > 0 {
			fl.bad = true
		}
	}()
	if fl.bad {
		return errOutOfRange
	}
	return nil
}

// NotExcusedThroughResult has a literal whose ends depend on a call nothing
// predicts but give the same result.
//
// @Ensures True
func NotExcusedThroughResult(n int) (err error) { // want `the contract of NotExcusedThroughResult may also be met by a function that always returns an error`
	bad := func() bool {
		if outsideNumber() > 0 {
			return n > 0
		}
		return n > 0
	}()
	if bad {
		return errOutOfRange
	}
	return nil
}
