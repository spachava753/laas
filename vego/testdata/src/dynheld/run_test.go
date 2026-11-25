package dynheld

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"
)

// TestClaims runs the verified programs and checks what their contracts
// say against Go's own assertions and switches.
func TestClaims(t *testing.T) {
	shapes := []Shape{nil, Circle{R: 4}, Rect{W: 2, H: 3}, &Square{S: 2}, NilSquare()}
	for _, sh := range shapes {
		_, isCircle := sh.(Circle)
		_, isRect := sh.(Rect)
		k := Kind(sh)
		if (k == 0) != (sh == nil) || (k == 1) != isCircle || (k == 2) != isRect {
			t.Errorf("Kind(%#v) = %d", sh, k)
		}
		if c, ok := sh.(Circle); ok && Radius(sh) != c.R || !ok && Radius(sh) != 0 {
			t.Errorf("Radius(%#v) = %d", sh, Radius(sh))
		}
		if AreaOf(sh) < 0 {
			t.Errorf("AreaOf(%#v) < 0", sh)
		}
	}
	if Width(Rect{W: 7}) != 7 || TwoShapes() != 14 || TwoShapesSwapped() != 14 || !NilSquareIsNotNil() {
		t.Error("Width, TwoShapes, TwoShapesSwapped, or NilSquareIsNotNil")
	}
	if c, ok := MakeCircle(9).(Circle); !ok || c.R != 9 {
		t.Error("MakeCircle")
	}
	for _, v := range []any{nil, 3, "abc", []byte("ab"), Point{X: 1}, 2.5} {
		n, ok := Int(v)
		i, isInt := v.(int)
		if ok != isInt || n != i {
			t.Errorf("Int(%#v) = %d, %v", v, n, ok)
		}
		k := Classify(v)
		switch v.(type) {
		case int:
			if k != 1 {
				t.Errorf("Classify(%#v) = %d", v, k)
			}
		case string:
			if k != 2 || Length(v) != len(v.(string)) {
				t.Errorf("Classify or Length(%#v)", v)
			}
		case Point:
			if k != 4 {
				t.Errorf("Classify(%#v) = %d", v, k)
			}
		case nil:
			if k != 0 {
				t.Errorf("Classify(nil) = %d", k)
			}
		}
	}
	if XOf(Point{X: 8}) != 8 || TwoValues() != 12 || TwoValuesSwapped() != 12 || PointBack() != 5 || Counted() != 3 {
		t.Error("XOf, TwoValues, TwoValuesSwapped, PointBack, or Counted")
	}
	if CodeThroughAny(&CodeErr{Code: 4}) != 4 || CodeMade() != 7 {
		t.Error("CodeThroughAny or CodeMade")
	}
	if First([]any{4, 5}) != 4 || Sum([]any{1, 2, 3}) != 6 {
		t.Error("First or Sum")
	}
}

// TestRefusedWouldFail shows what the refused programs would have claimed
// falsely.
func TestRefusedWouldFail(t *testing.T) {
	func() {
		defer func() {
			if recover() == nil {
				t.Error("MustInt of a string did not panic")
			}
		}()
		MustInt("x")
	}()
	if Claims(2) == 1 || !NamedApartIsTrue() {
		t.Error("Claims or NamedApart")
	}
	var buf bytes.Buffer
	if Grew(&buf, &buf) != 1 {
		t.Error("Grew of one buffer twice did not grow it")
	}
	name := filepath.Join(t.TempDir(), "f")
	if err := os.WriteFile(name, []byte("x"), 0o600); err != nil {
		t.Fatal(err)
	}
	f, err := os.Open(name)
	if err != nil {
		t.Fatal(err)
	}
	if Twice(f) == nil {
		t.Error("Twice closed the file once")
	}
}

// NamedApartIsTrue checks NamedApart and AliasSame against Go.
func NamedApartIsTrue() bool {
	n, ok := AliasSame()
	return !NamedApart() && ok && n == 1 && !Instances()
}
