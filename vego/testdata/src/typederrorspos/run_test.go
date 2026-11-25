package typederrorspos

import "testing"

// TestRefusedWouldFail shows what a proof of the functions that S0 of F34
// refuses would have claimed falsely: UsesPos verified before it, and the
// Pos that handsPos holds returns -1.
func TestRefusedWouldFail(t *testing.T) {
	if UsesPos() >= 0 || UsesPosMust() >= 0 || UsesPosSwitch() >= 0 {
		t.Error("the Pos that handsPos holds met its contract")
	}
	if SizeOf() >= 0 || FromMap() >= 0 || CallsPosFunc() >= 0 {
		t.Error("what handsSizer, handsMap, or handsPosFunc returns met its contract")
	}
	if HoldsAnError(nil) != true || HoldsAnError(&HookErr{}) != false {
		t.Error("HoldsAnError does not meet its contract")
	}
	pe := error(&PosErr{})
	if !IsPosErr(pe) || IsPosErr(nil) || Classify(pe) != 1 || ClassifyUnused(pe) != 1 || ClassifyUnused(&HookErr{}) != 2 || FindsNoPos() {
		t.Error("the forms that take nothing out do not meet their contracts")
	}
}
