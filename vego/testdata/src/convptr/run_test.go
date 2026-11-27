package convptr

import "testing"

func TestFalse(t *testing.T) {
	if Conv() == 2 {
		t.Error("Conv held")
	}
	if ConvFunc() == 2 {
		t.Error("ConvFunc held")
	}
	if Weaker() == 1 {
		t.Error("Weaker held")
	}
}
