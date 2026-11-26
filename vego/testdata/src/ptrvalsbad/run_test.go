package ptrvalsbad

import "testing"

// TestRefused shows that the claims refused in this package are false at
// run time, where Go can show it.
func TestRefused(t *testing.T) {
	x := 4
	KeepsOther(&x, &x)
	if x == 4 {
		t.Errorf("KeepsOther with p = q did not change what q points to")
	}
	if Converted() == 1 {
		t.Errorf("Converted did not write x through the *int")
	}
	if DeferredResultWrong() == 1 || CapturedWrong() == 1 {
		t.Errorf("a refused claim held at run time")
	}
	c := Counter(0)
	o := &Owner{c: &c}
	useOwner(o, (*int)(o.c))
	if *o.c == 0 {
		t.Errorf("useOwner did not write what o owns through p")
	}
}
