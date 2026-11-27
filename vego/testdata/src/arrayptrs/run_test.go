package arrayptrs

import "testing"

// Each defect's claim is false of a run, or it panics.
func TestDefects(t *testing.T) {
	b := &Block{Word: [4]uint32{0, 0, 1}}
	Wrong(b)
	if b.Word[2] == 1 {
		t.Error("Wrong: the write kept the element")
	}
	s := &Stack{items: []int{5, 0}}
	if s.Stale() == 5 {
		t.Error("Stale: the pointer read the old value")
	}
	for name, f := range map[string]func(){"NilIndex": func() { NilIndex() }, "NilDeref": func() { NilDeref() },
		"NilRangeValues": func() { NilRangeValues() }, "Short": func() { Short([]int{1, 2}) }, "NilRangeWrite": NilRangeWrite} {
		func() {
			defer func() {
				if recover() == nil {
					t.Errorf("%s did not panic", name)
				}
			}()
			f()
		}()
	}
	if NilRange() != 4 || NilLen() != 4 {
		t.Error("a nil pointer to an array has no length 4")
	}
}
