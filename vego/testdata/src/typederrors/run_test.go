package typederrors

import (
	"errors"
	"testing"
)

// TestClaims runs the functions of the package whose contracts vego proves
// and checks what they claim against Go: each canonical-term equality the
// verifier proves is Go's == on the real errors (F33).
func TestClaims(t *testing.T) {
	check := func(name string, got, want bool) {
		if got != want {
			t.Errorf("%s returned %v, and its proved contract says %v", name, got, want)
		}
	}
	check("Same", Same(), true)
	check("SameThroughAlias", SameThroughAlias(), true)
	check("Differ", Differ(), false)
	check("DifferTypes", DifferTypes(), false)
	check("MadeDiffers", MadeDiffers(), false)
	check("MadeAfter", MadeAfter(), false)
	check("NilPointers", NilPointers(nil), true)
	p, q := &PE{}, &PE{}
	check("SamePointer", SamePointer(p), true)
	check("SamePointer nil", SamePointer(nil), true)
	check("OtherPointer", OtherPointer(p, q), false)
	check("OtherPointer nil", OtherPointer(nil, q), false)
	for _, s := range []string{"", "a", "ab"} {
		check("Strings "+s, Strings(s), true)
	}
	check("StringsDiffer", StringsDiffer(), false)
	for _, a := range []int{-1, 0, 1} {
		for _, c := range []int{-1, 0, 1} {
			check("Pairs", Pairs(a, c), a == c)
		}
	}
	for n := -1; n <= 3; n++ {
		check("Switch", Switch(n), n == 2)
	}
	if Ret() == nil || NilPointerIsNotNil() == nil {
		t.Error("a conversion of a value of a concrete type is nil")
	}
}

func TestNotContradictory(t *testing.T) {
	if !NotContradictory(1) {
		t.Error("two errors of two types are equal")
	}
}

// TestFormulaClaims checks what the contracts of formulas.go say of the
// errors the functions return.
func TestFormulaClaims(t *testing.T) {
	for n := -2; n <= 2; n++ {
		err := Parse(n)
		if (err == nil) != (n >= 0) || n < 0 && err != ErrSyntax {
			t.Errorf("Parse(%d) = %v", n, err)
		}
		if ParseFailed(n) != (n < 0) || CallerDiffers(n) {
			t.Errorf("ParseFailed or CallerDiffers(%d)", n)
		}
		located := Located(n)
		if pe, ok := located.(*PE); (located == nil) != (n == 0) || n != 0 && (!ok || pe.Line != n) {
			t.Errorf("Located(%d) = %v", n, located)
		}
	}
	if _, ok := NotLocated().(*PE); ok {
		t.Error("NotLocated holds a *PE")
	}
	for _, src := range [][]byte{nil, {7}, {1, 200}} {
		first, some := FirstByte(src), SomeByte(src)
		if (first == nil) != (len(src) == 0) || len(src) > 0 && first != InvalidByteError(src[0]) {
			t.Errorf("FirstByte(%v) = %v", src, first)
		}
		found := false
		for _, b := range src {
			found = found || some == InvalidByteError(b)
		}
		if (some == nil) != (len(src) == 0) || len(src) > 0 && !found {
			t.Errorf("SomeByte(%v) = %v", src, some)
		}
		if !SomeByteNotSyntax(src) {
			t.Errorf("SomeByteNotSyntax(%v)", src)
		}
	}
	for _, s := range []string{"", "x"} {
		if err := Named(s); (err == nil) != (s == "") || s != "" && err != SErr(s) {
			t.Errorf("Named(%q) = %v", s, err)
		}
	}
	if !VariableHolds() || ReturnsVariable() != ErrVar {
		t.Error("ErrVar does not hold the error that holds ErrSyntax")
	}
	if !ReadsHeld(ErrSyntax) || ReadsHeld(ErrRange) || PassRange(ErrRange) != nil || PassRange(ErrSyntax) == nil {
		t.Error("ReadsHeld or PassRange")
	}
}

func TestLabelIsNotNamed(t *testing.T) {
	if LabelIsNotNamed("x") == SErr("x") {
		t.Error("a Label is an SErr")
	}
}

// TestRefusedWouldFail runs functions whose conversions are refused, and
// shows what a proof of them would have claimed falsely: consume runs the
// code the errors hold under an entry that modifies nothing.
func TestRefusedWouldFail(t *testing.T) {
	if ThroughAny() != 1 || ThroughHidden() != 1 {
		t.Error("consume did not bump the counter an error holds")
	}
	defer func() {
		if recover() == nil {
			t.Error("NilRuns did not panic")
		}
	}()
	NilRuns()
}

// TestAssertionClaims checks what the contracts of assert.go say.
func TestAssertionClaims(t *testing.T) {
	for n := -2; n <= 2; n++ {
		if LineOf(n) != n || NotAnError(n) || AsError(n) != (n != 0) {
			t.Errorf("LineOf, NotAnError, or AsError(%d)", n)
		}
		if n != 0 && MustLineOf(n) != n {
			t.Errorf("MustLineOf(%d)", n)
		}
		k := Kind(n)
		if (k == 0) != (n == 0) || n < 0 && k != 2 || n > 0 && k != 1 {
			t.Errorf("Kind(%d) = %d", n, k)
		}
		if (KindWithin(n) == 0) != (n == 0) {
			t.Errorf("KindWithin(%d)", n)
		}
	}
}

func TestAssertionZero(t *testing.T) {
	if !ZeroWhenNot(0) || MadeNotTyped() {
		t.Error("ZeroWhenNot or MadeNotTyped")
	}
}

// TestOriginClaims checks what the contracts of origin.go say against the
// real errors.Is and fmt.Errorf.
func TestOriginClaims(t *testing.T) {
	for n := -2; n <= 2; n++ {
		if IsSyntax(n) != (n < 0) || IsRange(n) || DirectIs(n) != (n < 0) {
			t.Errorf("IsSyntax, IsRange, or DirectIs(%d)", n)
		}
		if (Chained(n) == nil) != (n == 0) {
			t.Errorf("Chained(%d)", n)
		}
	}
	if Text(-1) == "" || WrapsByte(nil) != nil || WrapsByte([]byte{1}) == nil {
		t.Error("Text or WrapsByte")
	}
}

func TestWrapsByteIs(t *testing.T) {
	if !errors.Is(WrapsByteIs([]byte{7}), InvalidByteError(7)) || WrapsByteIs(nil) != nil {
		t.Error("WrapsByteIs")
	}
}

// TestAsClaims checks what the contracts of as.go say against the real
// errors.As and errors.AsType.
func TestAsClaims(t *testing.T) {
	for n := -2; n <= 2; n++ {
		if AsLine(n) != n || AsWrapped(n) != n || AsTypeLine(n) != n || AsOtherType(n) || AsCode(n) != (n < 0) {
			t.Errorf("AsLine, AsWrapped, AsTypeLine, AsOtherType, or AsCode(%d)", n)
		}
		var pe *PE
		if (SaysAs(n) == nil) != (n == 0) || n != 0 && !errors.As(SaysAs(n), &pe) || ReadsSaysAs(n) != (n != 0) {
			t.Errorf("SaysAs or ReadsSaysAs(%d)", n)
		}
	}
	if AsMade() || ValueHasNoIs() || ValueAsOther() || AsKeepsTarget() != 5 {
		t.Error("AsMade, ValueHasNoIs, or ValueAsOther")
	}
}
