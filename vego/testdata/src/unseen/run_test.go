package unseen

import "testing"

// TestRefusedWouldFail runs the functions whose proofs are refused, and
// shows that their contracts would be false: the methods nobody verified
// write what the value holds.
func TestRefusedWouldFail(t *testing.T) {
	if MadeHere() || DataKept([]byte{1}) || Wrapped() {
		t.Error("a method of the SDK did not write what its value holds")
	}
}

// TestVerified checks the claims of the functions that verify.
func TestVerified(t *testing.T) {
	if Handle("a") == nil || len(HandleLocal("a").Content) != 1 || Keep("a").Code != 200 || Back("a") != "a" || !Sent([]byte{1}) || Own("a") == nil {
		t.Error("a verified claim does not hold")
	}
	SentTwice("a")
	if FirePlain(3) != 3 {
		t.Error("FirePlain")
	}
}
