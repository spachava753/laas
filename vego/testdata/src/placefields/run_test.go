package placefields

import "testing"

// The claims the corpus expects not to be proved are false.
func TestFalseClaims(t *testing.T) {
	a := &A{}
	if SameField(a, a); a.X == 1 {
		t.Error("SameField held for one value")
	}
	b := &B{}
	if InsideWrong(b, &b.In); b.In.X == 0 {
		t.Error("InsideWrong held")
	}
	if Stale(&C{}, 1).X == 0 {
		t.Error("Stale held")
	}
}
