package appendloops

import "testing"

// When q points to b.Items, the store through q replaces b.Items by
// another slice at each iteration, so b.Items does not grow by n.
func TestOverwrites(t *testing.T) {
	b := &B{Items: []int{1}}
	Overwrites(b, &b.Items, nil, 2)
	if len(b.Items) == 3 {
		t.Error("b.Items grew by n though q points to it")
	}
}

// Cleared writes into the spare capacity of c.Items, which it does not
// list.
func TestCleared(t *testing.T) {
	c := &B{Items: make([]int, 1, 4)}
	Cleared(&B{}, c, 2)
	if c.Items[:2][1] != 1 {
		t.Error("Cleared did not write the spare capacity of c.Items")
	}
}
