package addrunsafeslice

import "testing"

func TestKeep(t *testing.T) {
	s := &S{}
	Keep(Leak(s), s)
	if s.n == 0 {
		t.Error("Keep held")
	}
}
