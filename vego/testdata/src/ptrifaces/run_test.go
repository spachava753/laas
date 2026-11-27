package ptrifaces

import "testing"

// The claims the corpus expects not to be proved are false.
func TestFalseClaims(t *testing.T) {
	c := &Counter{}
	KeepsCounter(c)
	if c.N == 0 {
		t.Error("KeepsCounter held")
	}
	c = &Counter{}
	KeepsOther(c, c)
	if c.N == 0 {
		t.Error("KeepsOther held for one counter")
	}
}
