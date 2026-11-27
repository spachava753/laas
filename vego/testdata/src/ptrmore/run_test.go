package ptrmore

import "testing"

// The claims the corpus expects not to be proved are false.
func TestFalseClaims(t *testing.T) {
	xs := []string{}
	KeepsOther(&xs, &xs)
	if len(xs) == 0 {
		t.Error("KeepsOther held")
	}
	if NodeWrong() == nil {
		t.Error("NodeWrong held")
	}
	if RunWrong(false) != nil {
		t.Error("RunWrong held")
	}
	if CountsWrong() == nil {
		t.Error("CountsWrong held")
	}
}
