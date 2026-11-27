package boxconv

import "testing"

func TestFalse(t *testing.T) {
	xs := []Hits{7, 8}
	ConvertElemValue(xs)
	if xs[0] == 42 {
		t.Error("ConvertElemValue held")
	}
	ConvertElem(xs)
	TwoElems(xs)
	TwoConverted(xs)
	t.Log("ConvertElem, TwoElems, and TwoConverted returned, so their Ensures False is false")
}
