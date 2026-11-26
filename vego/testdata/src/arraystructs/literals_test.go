package arraystructs

import "testing"

// TestLiterals checks the contracts of the ways of making Cells.
func TestLiterals(t *testing.T) {
	if r := MakeLiteral(); len(r) != 1 || r[0].buf != [4]byte{} {
		t.Errorf("MakeLiteral returned %v", r)
	}
	if r := MakeMake(3); len(r) != 3 || r[2].buf[3] != 0 {
		t.Errorf("MakeMake returned %v", r)
	}
	if r := MakeAppend(nil); len(r) != 1 || r[0].buf[2] != 5 {
		t.Errorf("MakeAppend returned %v", r)
	}
	if r := MakeHolder(); r.c.buf[3] != 9 || r.c.buf[0] != 0 {
		t.Errorf("MakeHolder returned %v", r)
	}
	xs := []Cell{{buf: [4]byte{1, 1, 1, 1}}}
	Assign(xs)
	if xs[0].buf[3] != 4 || xs[0].buf[0] != 0 {
		t.Errorf("Assign left %v", xs[0])
	}
}
