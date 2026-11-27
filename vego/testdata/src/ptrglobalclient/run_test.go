package ptrglobalclient

import "testing"

func TestUse(t *testing.T) {
	if Use() == 0 {
		t.Error("Use's claim held")
	}
}
