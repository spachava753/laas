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

// TestInside shows why the calls of A9 to A11 are refused: the callee is
// handed, or each result holds, memory inside what the owner owns.
func TestInside(t *testing.T) {
	r := MakeItems()
	writePoint(r, &r.items[0].point)
	if r.items[0].point.x == 0 {
		t.Errorf("writePoint did not write the owned Point")
	}
	r = MakeItems()
	if got := project(r.items); got[0] != &r.items[0].point {
		t.Errorf("project's result does not point into what it was handed")
	}
	h := &Lists{l: make(List, 1)}
	if w := wrap(h.l); &w[0][0] != &h.l[0] {
		t.Errorf("wrap's result does not hold what it was handed")
	}
}
