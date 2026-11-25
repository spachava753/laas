package tables

import "testing"

func TestChanges(t *testing.T) {
	tested[0] = 3
	if Tested() != 3 {
		t.Fatal("not changed")
	}
}
