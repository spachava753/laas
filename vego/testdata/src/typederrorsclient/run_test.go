package typederrorsclient

import (
	"errors"
	"testing"

	"typederrors"
)

// TestClaims checks what the contracts of the package say, read from the
// contracts of typederrors, against Go (S2 of F33).
func TestClaims(t *testing.T) {
	for n := -2; n <= 2; n++ {
		if Failed(n) != (n < 0) || NotRange(n) {
			t.Errorf("Failed or NotRange(%d)", n)
		}
		if err := Forward(n); (err == nil) != (n >= 0) || n < 0 && err != typederrors.ErrSyntax {
			t.Errorf("Forward(%d) = %v", n, err)
		}
		err := ForwardLocated(n)
		if pe, ok := err.(*typederrors.PE); (err == nil) != (n == 0) || n != 0 && (!ok || pe.Line != n) {
			t.Errorf("ForwardLocated(%d) = %v", n, err)
		}
		if Found(n) != n {
			t.Errorf("Found(%d)", n)
		}
		found := ForwardFound(n)
		if pe, ok := found.(*typederrors.PE); (found == nil) != (n >= 0) || n < 0 && (!ok || pe.Line != n) {
			t.Errorf("ForwardFound(%d) = %v", n, found)
		}
	}
	if err := ForwardByte([]byte{9}); err != typederrors.InvalidByteError(9) {
		t.Errorf("ForwardByte = %v", err)
	}
}

func TestWraps(t *testing.T) {
	for n := -1; n <= 1; n++ {
		if err := Wraps(n); (err == nil) != (n >= 0) || n < 0 && !errors.Is(err, typederrors.ErrSyntax) {
			t.Errorf("Wraps(%d) = %v", n, err)
		}
	}
}
