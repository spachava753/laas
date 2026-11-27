package sliceviewq

import (
	"testing"

	"sliceviewp"
)

// What the assumption excludes: Both's claim is false for a view of s.
func TestBoth(t *testing.T) {
	s := &sliceviewp.S{}
	sliceviewp.Both(View(s), s)
	if s.N == 0 {
		t.Error("Both held")
	}
}
