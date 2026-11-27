package ownsptr

import "testing"

// What the refusals keep from being proved is false.
func TestOwned(t *testing.T) {
	s := &Stack{items: []int{0}}
	SetOwn(s)
	if s.items[0] == 1 {
		t.Error("Set's claim held for a pointer into what s owns")
	}
	o := &Outer{in: &Inner{}}
	SetInOwn(o)
	if o.in.n == 1 {
		t.Error("SetIn's claim held for a pointer into what o owns")
	}
}
