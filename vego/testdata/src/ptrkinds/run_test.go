package ptrkinds

import "testing"

func TestTrue(t *testing.T) {
	s, h := &S{A: 1, B: 2}, &H{}
	ThroughId(s)
	ThroughField(s, h)
	CountThroughField(s, h)
	if s.A != 9 || s.B != 2 {
		t.Error(s)
	}
}
