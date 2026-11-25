package replacedc

import "testing"

// negative meets the replacement of Read: it says nothing of n.
type negative struct{}

func (negative) Read(p []byte) (int, error) { return -1, nil }

// TestReadOnePanics shows what the replacement, resting unseen under the
// shipped entries of bufio, would have let through.
func TestReadOnePanics(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("ReadOne returned; the run should show the panic the replacement allows")
		}
	}()
	_, _ = ReadOne(negative{})
}
