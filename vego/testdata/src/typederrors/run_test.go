package typederrors

import "testing"

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
