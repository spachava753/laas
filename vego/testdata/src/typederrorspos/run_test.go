package typederrorspos

import "testing"

// TestRefusedWouldFail shows what a proof of the functions that S0 of F34
// refuses would have claimed falsely: UsesPos verified before it, and the
// Pos that handsPos holds returns -1.
func TestRefusedWouldFail(t *testing.T) {
	if UsesPos() >= 0 || UsesPosMust() >= 0 || UsesPosSwitch() >= 0 {
		t.Error("the Pos that handsPos holds met its contract")
	}
	if HoldsAnError(nil) != true || HoldsAnError(&HookErr{}) != false {
		t.Error("HoldsAnError does not meet its contract")
	}
}
