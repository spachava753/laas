package dyneq

import (
	"errors"
	"testing"
)

// TestClaims runs the verified programs against Go.
func TestClaims(t *testing.T) {
	for v, want := range map[any]bool{3: true, 4: false, "3": false, int64(3): false, nil: false} {
		if IsThree(v) != want {
			t.Errorf("IsThree(%#v)", v)
		}
	}
	if !IsX("x") || IsX(3) {
		t.Error("IsX")
	}
	if a, b, c := Compared(); !a || b || c {
		t.Error("Compared")
	}
	if a, b, c := ComparedSwapped(); !a || b || c {
		t.Error("ComparedSwapped")
	}
	if !SameInts(2, 2) || SameInts(2, 3) {
		t.Error("SameInts")
	}
	if a, b := Nils(); !a || b {
		t.Error("Nils")
	}
	if !IsUnitCircle(Circle{R: 1}) || IsUnitCircle(Circle{R: 2}) || IsUnitCircle(Rect{}) || IsUnitCircle(nil) {
		t.Error("IsUnitCircle")
	}
	if a, b, c := Shapes(); !a || b || c {
		t.Error("Shapes")
	}
	if a, b := ShapesSwapped(); !a || b {
		t.Error("ShapesSwapped")
	}
	if NotZero(0) || !NotZero(1) || !NotZero("0") {
		t.Error("NotZero")
	}
	if a, b := Pointers(); !a || b {
		t.Error("Pointers")
	}
	if Name(nil) != 0 || Name(1) != 1 || Name("one") != 2 || Name(2) != 3 {
		t.Error("Name")
	}
	if k, n := Names(); k != 2 || n != 1 {
		t.Error("Names")
	}
	if !Matches(3, 3) || Matches(3, 4) || Matches(3, "3") {
		t.Error("Matches")
	}
	if !ErrInAny() || OtherErr() {
		t.Error("ErrInAny or OtherErr")
	}
	if !TwoPathsEq(true) || !TwoPathsEq(false) {
		t.Error("TwoPathsEq")
	}
	if IntAndInt64Honest() || !GoEq(5, 5) || GoEq(5, 6) {
		t.Error("IntAndInt64Honest or GoEq")
	}
}

// TestRefusedWouldFail shows that the refused and unproved programs claim
// what Go does not do.
func TestRefusedWouldFail(t *testing.T) {
	panics := func(name string, f func()) {
		defer func() {
			if recover() == nil {
				t.Errorf("%s did not panic", name)
			}
		}()
		f()
	}
	panics("Eq of two slices", func() { Eq([]int{1}, []int{1}) })
	panics("Slices", func() { Slices([]int{1}, []int{1}) })
	panics("BlankSlice", func() { BlankSlice() })
	panics("HolderEq", func() { HolderEq(Holder{X: []int{1}}) })
	if NaN() || NaNErr() || IntAndInt64() || !SameThree() || OtherFour() || ParamIsThree(4) || NameOfTwo() == 1 {
		t.Error("NaN, IntAndInt64, SameThree, OtherFour, ParamIsThree, or NameOfTwo")
	}
	p := &Circle{}
	if a, b := Differ(p); a != b {
		t.Error("Differ gives values that Go's != tells apart")
	}
	_ = errors.New
}
