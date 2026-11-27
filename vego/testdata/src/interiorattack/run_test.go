package interiorattack

import "testing"

func TestFalseClaims(t *testing.T) {
	s := &S{}
	SameField(s)
	if s.a == 1 {
		t.Error("SameField's claim held")
	}
	if CallAliased() == 1 {
		t.Error("CallAliased's claim held")
	}
	s = &S{a: 3}
	IncAOnly(s)
	if s.a == 3 {
		t.Error("IncAOnly's claim held")
	}
	if ArrayElems(1, 1) == 1 {
		t.Error("ArrayElems's claim held")
	}
	xs := make([]int, 2)
	if KeptAcrossMove(xs) == 5 {
		t.Error("KeptAcrossMove's claim held")
	}
	if CopyBeside(&S{}) == 1 {
		t.Error("CopyBeside's claim held")
	}
	if LocalCopy() == 1 {
		t.Error("LocalCopy's claim held")
	}
	o := &Holder{items: []Item{{n: 1}}}
	DeepFalse(o, 0, 0)
	if o.items[0].n == 1 {
		t.Error("DeepFalse's claim held")
	}
	if CallSliceAndPointer() == 1 {
		t.Error("CallSliceAndPointer's claim held")
	}
	st := &Stats{Hits: 4}
	AddHitFalse(st)
	if st.Hits == 4 {
		t.Error("AddHitFalse's claim held")
	}
}

func TestTrueClaims(t *testing.T) {
	s := &S{}
	TwoFields(s)
	if s.a != 1 || s.b != 2 {
		t.Error("TwoFields")
	}
	xs := make([]int, 1, 2)
	if KeptInPlace(xs) != 5 {
		t.Error("KeptInPlace")
	}
	if ArrayElemsApart(0, 1) != 1 {
		t.Error("ArrayElemsApart")
	}
}
