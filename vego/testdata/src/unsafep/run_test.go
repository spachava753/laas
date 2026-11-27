package unsafep

import "testing"

// Keep's claim is false after Leak.
func TestKeep(t *testing.T) {
	s := &S{}
	Keep(Leak(s), s)
	if N(s) == 0 {
		t.Error("Keep held after Leak")
	}
}
