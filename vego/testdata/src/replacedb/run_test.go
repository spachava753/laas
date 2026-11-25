package replacedb

import (
	"io"
	"testing"
)

// TestFlushesPanics shows that what the weaker replacement of Write would
// prove of Flushes is false: it panics.
func TestFlushesPanics(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("Flushes returned; the refused proof would say it does not panic, and the run should show it does")
		}
	}()
	_ = Flushes()
}

var on bool

// flip is an error whose Is answers differently each time.
type flip struct{}

func (flip) Error() string { return "flip" }
func (flip) Is(error) bool { on = !on; return on }

// one meets the entry of Read: it reads one byte.
type one struct{}

func (one) Read(p []byte) (int, error) { p[0] = 'x'; return 1, nil }

// failing meets the shipped entry of Write, which vouches for nothing.
type failing struct{}

func (failing) Write(p []byte) (int, error) { return 0, flip{} }

var _ io.Writer = failing{}

// TestTwiceRefused shows that what the replacement of Read would prove of
// Twice is false.
func TestTwiceRefused(t *testing.T) {
	if a, b := Twice(one{}, failing{}); a == b {
		t.Fatalf("Twice = %v, %v; the refused proof would say they are equal, and the run should show them apart", a, b)
	}
}
