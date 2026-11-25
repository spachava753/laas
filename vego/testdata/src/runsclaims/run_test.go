package runsclaims

import "testing"

// TestFalseEntry shows what the false entry of use lets through: Hands
// verifies with r = 0, and returns 1.
func TestFalseEntry(t *testing.T) {
	if r := Hands(); r != 1 {
		t.Fatalf("Hands returned %d; the corpus shows that it returns 1 under the false entry of use", r)
	}
}

// TestRefusedWouldFail runs the functions whose calls are refused, and
// shows that their contracts would be false.
func TestRefusedWouldFail(t *testing.T) {
	if HandsBump() != 1 || HandsShut() != 1 || HandsInError() != 1 || HandsHook() != 1 {
		t.Error("a trusted function did not run the code it finds by a type assertion")
	}
	if BoxedAny(failing{0}) != 1 {
		t.Error("consumeAny did not run Error")
	}
}

// TestVerified checks the claims of the functions that verify.
func TestVerified(t *testing.T) {
	if HandsPing() != 0 || !AskTimeout() || HandsHolder() != 0 {
		t.Error("HandsPing or AskTimeout")
	}
}

// TestDeeperRefused runs the functions whose calls are refused for what a
// parameter reaches beyond its fields' first interface.
func TestDeeperRefused(t *testing.T) {
	if HandsTwo() != 1 || HandsNext() != 1 || HandsLatch() != 1 {
		t.Error("a trusted function did not run the code it finds on what a parameter reaches")
	}
}
