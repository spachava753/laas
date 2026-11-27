package memory

import "testing"

// What ResetBoxed claims is false when s is a view of p.A.
func TestResetBoxed(t *testing.T) {
	p := &Boxed{A: [1]int{7}}
	if ResetBoxed(p, p.A[:]) == 7 {
		t.Error("the slice kept 7 though the struct it views was overwritten")
	}
}
