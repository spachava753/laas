package unsafeassumedq

import (
	"testing"

	"unsafeassumed"
)

// What the assumption excludes: Keep's claim is false after Field.
func TestKeep(t *testing.T) {
	s := &unsafeassumed.S{}
	unsafeassumed.Keep(Field(s), s)
	if unsafeassumed.N(s) == 0 {
		t.Error("Keep held after Field")
	}
}
