package s1pairs

import "testing"

// The claims the corpus expects not to be proved are false.
func TestFalseClaims(t *testing.T) {
	tg := &Tagged{}
	if ThroughPlainWrong(tg); tg.X == 0 {
		t.Error("ThroughPlainWrong held")
	}
	pl := &Plain{}
	if ThroughTaggedWrong(pl); pl.Y == 0 {
		t.Error("ThroughTaggedWrong held")
	}
	m := &Meter{}
	if Keep((*int)(&m.c), m); m.c == 0 {
		t.Error("Keep held")
	}
}
