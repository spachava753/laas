package dynifaces

import (
	"errors"
	"testing"
)

// TestClaims runs the verified programs against Go.
func TestClaims(t *testing.T) {
	if ok, ok2 := CircleNamedSquareNot(); !ok || ok2 {
		t.Error("CircleNamedSquareNot")
	}
	if ok, ok2 := SquareNotCircleNamed(); ok || !ok2 {
		t.Error("SquareNotCircleNamed")
	}
	if ok, ok2 := ShapeOrNot(); !ok || ok2 {
		t.Error("ShapeOrNot")
	}
	for v, k := range map[any]int{nil: 0, 3: 1, Circle{}: 2, Square{}: 2, &CodeErr{}: 4, "s": 5} {
		if Kind(v) != k {
			t.Errorf("Kind(%#v) = %d", v, Kind(v))
		}
	}
	if k, n := ShapeFirst(); k != 2 || n != 3 {
		t.Error("ShapeFirst")
	}
	if ok, ok2, ok3 := ErrorsInAny(); !ok || ok2 || !ok3 {
		t.Error("ErrorsInAny")
	}
	if r, ok := MaybeReader(nil); r != nil || ok {
		t.Error("MaybeReader(nil)")
	}
	if ok, ok2 := TimeoutOrNot(); !ok || ok2 {
		t.Error("TimeoutOrNot")
	}
	if ok, ok2 := NotThenTimeout(); ok || !ok2 {
		t.Error("NotThenTimeout")
	}
	if !TimeoutLiteral() || !BackToConcrete() {
		t.Error("TimeoutLiteral or BackToConcrete")
	}
	if tt, ok := AsTimeouter(errors.New("x")); tt != nil || ok {
		t.Error("AsTimeouter")
	}
	if k, n := SwitchOnError(); k != 1 || n != 2 {
		t.Error("SwitchOnError")
	}
	if TimeouterOf(&TimeoutErr{}) == nil || TimeouterOf(errors.New("x")) != nil {
		t.Error("TimeouterOf")
	}
	if !ErrParamInAny(errors.New("x")) || ErrParamInAny(nil) {
		t.Error("ErrParamInAny")
	}
	if IsCoder(errors.New("x")) || IsCloser(errors.New("x")) {
		t.Error("IsCoder or IsCloser")
	}
}

// TestRefusedWouldFail shows that the refused and unproved programs claim
// what Go does not do.
func TestRefusedWouldFail(t *testing.T) {
	func() {
		defer func() {
			if recover() == nil {
				t.Error("the Error of what ConvertedThroughAny returns did not panic")
			}
		}()
		_ = ConvertedThroughAny().Error()
	}()
	if ok1, ok2 := TwoLocals(); !ok1 || ok2 {
		t.Error("TwoLocals")
	}
	if SquareNamed() || !CircleNotNamed() || !WrappedUnwraps() || NamedAfterShape() != 2 || !BackIsNot() {
		t.Error("SquareNamed, CircleNotNamed, WrappedUnwraps, NamedAfterShape, or BackIsNot")
	}
	if CodeOf(negErr{}) != -1 {
		t.Error("CodeOf of a negErr is not -1")
	}
	func() {
		defer func() {
			if recover() == nil {
				t.Error("MustReader(nil) did not panic")
			}
		}()
		MustReader(nil)
	}()
}

// negErr is an error of code that is not verified whose Code breaks the
// contract of Coder.
type negErr struct{}

func (negErr) Error() string { return "neg" }
func (negErr) Code() int     { return -1 }
