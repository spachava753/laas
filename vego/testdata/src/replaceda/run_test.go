package replaceda

import "testing"

// full meets the replacement of Read: it fills every buffer.
type full struct{}

func (full) Read(p []byte) (int, error) { return len(p), nil }

// TestReadTenRefused shows that what the replacement would prove of ReadTen
// is false: its reader meets the replacement, and ReadTen reads one byte.
func TestReadTenRefused(t *testing.T) {
	if n, err := ReadTen(full{}); n == 10 || err != nil {
		t.Fatalf("ReadTen = %d, %v; the refused proof would say n = 10 Or err != nil, and the run should show it false", n, err)
	}
}
