package reflectp

import "testing"

// Keep's claim is false after Leak.
func TestKeep(t *testing.T) {
	s := &S{}
	Keep(Leak(s), s)
	if s.n == 0 {
		t.Error("Keep held")
	}
}
