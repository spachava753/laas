package ptrvalsclient

import "testing"

// TestClaims checks the contracts that verify, through ptrvalslib.
func TestClaims(t *testing.T) {
	x := 3
	Twice(&x)
	if x != 5 || Local() != 1 {
		t.Errorf("Twice or Local returned what its contract does not say")
	}
}
