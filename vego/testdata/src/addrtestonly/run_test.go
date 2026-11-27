package addrtestonly

import "testing"

func TestKeep(t *testing.T) {
	s := &S{}
	Keep(&s.n, s)
	if s.n == 0 {
		t.Error("Keep held")
	}
}
