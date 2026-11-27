package arrayfields

import "testing"

// Each defect's claim is false of a run.
func TestDefects(t *testing.T) {
	xs := []Item{{}, {}, {}}
	Wrong(xs)
	if xs[1].Vals[2] == 5 {
		t.Error("Wrong: writing the first item changed the next")
	}
	xs = []Item{{}, {Vals: [4]int64{7}}}
	Bad(xs)
	if xs[1].Vals[0] == 7 {
		t.Error("Bad: the next item kept its value")
	}
	xs = []Item{{}, {Vals: [4]int64{0, 8}}, {}}
	CallerWrong(xs)
	if xs[1].Vals[1] == 8 {
		t.Error("CallerWrong: set kept what it wrote")
	}
	xs = []Item{{}, {Vals: [4]int64{0, 0, 0, 5}}, {}}
	LoopWrong(xs)
	if xs[1].Vals[3] == 5 {
		t.Error("LoopWrong: the loop kept a value it zeroed")
	}
	xs = []Item{{}, {Vals: [4]int64{0, 0, 5}}, {}}
	PtrWrong(xs)
	if xs[1].Vals[2] == 5 {
		t.Error("PtrWrong: the write through the pointer kept the element")
	}
	w := &Wide{Arr: [4]int64{1, 3, 1, 1}}
	NextChanged(w)
	if w.Arr[1] == 0 {
		t.Error("NextChanged: zero of the first element changed the second")
	}
	w = &Wide{Arr: [4]int64{1, 1, 1, 1}}
	SecondHalfZero(w)
	if w.Arr[2] == 0 {
		t.Error("SecondHalfZero: the second half was zeroed")
	}
}

// The claims about one position of two regions are false of a run.
func TestPlaces(t *testing.T) {
	s := &Shorts{C: [4]int16{5}}
	PlaceChangedElement(s)
	if s.C[0] == 1 {
		t.Error("PlaceChangedElement: writing B changed C[0]")
	}
	s = &Shorts{B: 5}
	ElementChangedPlace(s)
	if s.B == 1 {
		t.Error("ElementChangedPlace: writing C[0] changed B")
	}
	var x int16 = 4
	keepsWithout(&x, &x)
	if x == 4 {
		t.Error("keepsWithout: one value was kept though written")
	}
}

// WritesWithin's claim is false when p points to the element.
func TestWritesWithin(t *testing.T) {
	s := &Shorts{C: [4]int16{5}}
	WritesWithin(s, &s.C[0])
	if s.C[0] == 5 {
		t.Error("WritesWithin: the element kept its value")
	}
}
