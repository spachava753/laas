package typederrorspos

import "errors"

// A value with a contract taken out of an error (R1 of F34, S0). A typed
// error may hold a function value of a type with a contract, and code that
// is not verified may make one that does not meet it: handsPos is trusted
// with an entry that vouches for nothing, as an entry for a function that
// returns an error need not. Before S0, UsesPos verified, and it returns
// -1 (TestRefusedWouldFail).

// Pos maps an integer to one that is not negative.
//
// @Ensures y >= 0
type Pos func(x int) (y int)

// PosErr is an error that holds a Pos.
type PosErr struct{ F Pos }

// @Ensures True
func (e *PosErr) Error() (s string) { return "pos" }

// PosList is an error that holds Pos values in a slice.
type PosList struct{ Fs []Pos }

// @Ensures True
func (e *PosList) Error() (s string) { return "pos list" }

// handsPos is trusted: its entry says nothing of what the error holds.
func handsPos() error {
	return &PosErr{F: func(x int) (y int) { return -1 }}
}

// @Ensures r >= 0
func UsesPos() (r int) {
	if e, ok := handsPos().(*PosErr); ok && e != nil && e.F != nil { // want `cannot verify UsesPos: asserting an error to \*PosErr is not supported: it holds in field F a function value of type Pos, which has a contract, and nothing claims that a value taken out of an interface value meets that contract: code that is not verified may have made it`
		return e.F(1)
	}
	return 0
}

// @Ensures r >= 0
func UsesPosMust() (r int) {
	e := handsPos().(*PosErr) // want `cannot verify UsesPosMust: asserting an error to \*PosErr is not supported: it holds in field F a function value of type Pos`
	if e != nil && e.F != nil {
		return e.F(1)
	}
	return 0
}

// @Ensures r >= 0
func UsesPosSwitch() (r int) {
	switch e := handsPos().(type) {
	case *PosErr: // want `cannot verify UsesPosSwitch: a case of \*PosErr in a type switch is not supported: it holds in field F a function value of type Pos`
		if e != nil && e.F != nil {
			return e.F(1)
		}
	}
	return 0
}

// @Ensures r >= 0
func UsesPosList(err error) (r int) {
	if e, ok := err.(*PosList); ok && e != nil && len(e.Fs) > 0 && e.Fs[0] != nil { // want `cannot verify UsesPosList: asserting an error to \*PosList is not supported: it holds in field Fs a function value of type Pos`
		return e.Fs[0](1)
	}
	return 0
}

// @Ensures ~r
func FindsPos() (r bool) {
	var e *PosErr
	return errors.As(errors.New("x"), &e) // want `cannot verify FindsPos: errors.As with a target of \*PosErr is not supported: it holds in field F a function value of type Pos`
}

// @Ensures ~r
func FindsPosType() (r bool) {
	_, r = errors.AsType[*PosErr](errors.New("x")) // want `cannot verify FindsPosType: errors.AsType with a target of \*PosErr is not supported: it holds in field F a function value of type Pos`
	return r
}

// A type that holds a function value of a type without a contract is not
// such a type, and neither is one that holds an error: each value of an
// error that verified code makes is checked where it is made.

// HookErr holds an error.
type HookErr struct{ Inner error }

// @Ensures True
func (e *HookErr) Error() (s string) { return "hook" }

// @Ensures r <-> err = nil
func HoldsAnError(err error) (r bool) {
	if e, ok := err.(*HookErr); ok && e != nil {
		return false
	}
	return err == nil
}
