package ownstorage

import "testing"

// TestHandedApart checks the contracts of the callers that verify.
func TestHandedApart(t *testing.T) {
	if r := GetApart(MakeHolder()); r != 0 {
		t.Errorf("GetApart is proved to return 0, returned %d", r)
	}
}

// TestHandedOwned shows why the calls vego refuses are refused: each
// callee, handed what the owner owns through a converted type, changes
// what its contract says it leaves unchanged.
func TestHandedOwned(t *testing.T) {
	h := MakeHolder()
	use(h, (*B)(h.p))
	if h.p.n == 0 {
		t.Errorf("use did not write what h owns through b")
	}
	p := MakePile()
	useS(p, []int(p.items))
	if p.items[0] == 0 {
		t.Errorf("useS did not write what p owns through xs")
	}
	r := MakeRow()
	useA(r, (*B)(&r.as[0]))
	if r.as[0].n == 0 {
		t.Errorf("useA did not write what r owns through b")
	}
}
