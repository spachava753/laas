package apartptr

import "testing"

// Without apart the claims would be false; with within they hold.
func TestClaims(t *testing.T) {
	s := &S{n: 1}
	Keep(&s.n, s)
	if s.n == 1 {
		t.Error("Keep kept s.n through a pointer into s")
	}
	x := 0
	Two(&x, &x)
	if x == 1 {
		t.Error("Two kept *p through one number twice")
	}
	s = &S{n: 1}
	IntoWrong(s.Ptr(), s)
	if s.n == 1 {
		t.Error("IntoWrong held")
	}
}
