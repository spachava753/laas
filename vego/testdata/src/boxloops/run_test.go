package boxloops

import "testing"

func TestFalse(t *testing.T) {
	x := 1
	CountWrong(&x, 2)
	if x == 1 {
		t.Error("CountWrong held")
	}
	s := &S{A: 9}
	KeepB(&s.A, s, 2)
	if s.A == 9 {
		t.Error("KeepB held")
	}
}

func TestCalls(t *testing.T) {
	s := &S{A: 9}
	KeepCall(&s.A, s, 2)
	if s.A == 9 {
		t.Error("KeepCall held")
	}
	x := 1
	CountCall(&x, 2)
	if x == 1 {
		t.Error("CountCall held")
	}
}

func TestImprecise(t *testing.T) {
	s := &S{A: 9}
	Imprecise(&s.A, s, 2)
	if s.A == 9 {
		t.Error("Imprecise held")
	}
}
