package embedb

import (
	"embeda"
	"testing"
)

// Keep's claim is false through the promoted method.
func TestKeep(t *testing.T) {
	s := &embeda.S{}
	p := s.Ptr()
	embeda.Keep(p, s)
	if *s.Ptr() == 0 {
		t.Error("Keep's claim held")
	}
}
