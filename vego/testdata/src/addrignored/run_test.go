//go:build debug

package addrignored

import "testing"

// Keep's claim is false for the pointer to s.n that the debug build makes:
// go test -tags debug shows it. The file is behind the tag so that its own
// &s.n is not what makes the field addressable.
func TestKeep(t *testing.T) {
	s := &S{}
	Keep(N(s), s)
	if s.n == 0 {
		t.Error("Keep held")
	}
}
