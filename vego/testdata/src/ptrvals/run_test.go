package ptrvals

import "testing"

// TestClaims checks what the contracts of ptrvals say against Go.
func TestClaims(t *testing.T) {
	x := 3
	Inc(&x)
	if x != 4 {
		t.Errorf("Inc is proved to add 1, got %d", x)
	}
	if IncLocal() != 6 || IncNew() != 2 || ReadAfterWrite() != 2 || WriteThrough() != 3 {
		t.Errorf("a function of locals returned what its contract does not say")
	}
	p := 5
	Add(&p, &p)
	if p != 10 {
		t.Errorf("Add with p = q is proved to give *p + *q, got %d", p)
	}
	q := 1
	Swap(&q, &q)
	if q != 1 {
		t.Errorf("Swap with p = q is proved to keep the value, got %d", q)
	}
	if a, b := SwapLocals(); a != 2 || b != 1 {
		t.Errorf("SwapLocals is proved to return 2, 1, got %d, %d", a, b)
	}
	seven := 7
	if LimitOr(Config{Limit: &seven}, 1) != 7 || LimitOr(Config{}, 1) != 1 {
		t.Errorf("LimitOr returned what its contract does not say")
	}
	var c Config
	SetLimit(&c, 9)
	if c.Limit == nil || *c.Limit != 9 {
		t.Errorf("SetLimit is proved to set the limit to 9")
	}
	s := "a"
	Rename(&s, "b")
	b := true
	Toggle(&b)
	if s != "b" || b {
		t.Errorf("Rename or Toggle did not do what its contract says")
	}
	if n := NewInt(4); *n != 4 {
		t.Errorf("NewInt is proved to point to 4")
	}
	if CountTwice() != 2 {
		t.Errorf("CountTwice is proved to return 2")
	}
	k := Counter(1)
	Converted(&k)
	if k != 2 {
		t.Errorf("Converted is proved to add 1, got %d", k)
	}
	if DeferredResult() != 2 || SwitchedAddress(1) != 3 || TwoResults() != 3 || Captured() != 4 {
		t.Errorf("a function of boxed variables returned what its contract does not say")
	}
	if CountTrusted() != 2 {
		t.Errorf("CountTrusted is proved to return 2")
	}
}
