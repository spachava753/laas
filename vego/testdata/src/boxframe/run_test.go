package boxframe

import "testing"

func TestKeeps(t *testing.T) {
	xs := []Hits{0, 7}
	Keeps(xs)
	if xs[1] == 7 {
		t.Error("Keeps held")
	}
}
