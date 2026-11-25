package optional

import (
	"io"
	"testing"
)

// TestOddIsNoStringWriter shows that Go agrees that a WriteString of
// another signature does not implement io.StringWriter: io.WriteString
// calls Write.
func TestOddIsNoStringWriter(t *testing.T) {
	if OddAsks() {
		t.Fatal("Odd implements io.StringWriter")
	}
	if n, _ := io.WriteString(Odd{}, "ab"); n != 2 {
		t.Fatalf("io.WriteString(Odd{}, \"ab\") = %d; Write returns 2", n)
	}
}

// TestRefusedWouldFail shows, for each refused program, that what its
// contract would have claimed is false at run time.
func TestRefusedWouldFail(t *testing.T) {
	if n, _ := io.WriteString(BadAsWriter(), "x"); n <= 1 {
		t.Errorf("io.WriteString through BadAsWriter = %d; the entry of StringWriter allows at most 1", n)
	}
	if KeepsN(&Quiet{}) {
		t.Error("KeepsN = true; put calls WriteString, which counts")
	}
	if w, ok := PipeAsReader().(io.Writer); !ok {
		t.Error("Pipe is no writer")
	} else if n, _ := w.Write([]byte("x")); n >= 0 {
		t.Errorf("Write through PipeAsReader = %d", n)
	}
	checks := map[string]func() int{
		"FromSink":           FromSink,
		"ErrDirect":          ErrDirect,
		"FromAny":            func() int { return FromAny(io.Discard) },
		"ErrThroughAny":      ErrThroughAny,
		"VouchedThroughAny":  VouchedThroughAny,
		"ErrThroughStringer": ErrThroughStringer,
		"ErrorAsWriter":      ErrorAsWriter,
	}
	for name, f := range checks {
		if n := f(); n >= 0 {
			t.Errorf("%s = %d; its contract says n >= 0, and the run should show it false", name, n)
		}
	}
	if n, _ := io.WriteString(Through(), "x"); n >= 0 {
		t.Errorf("io.WriteString through Through = %d", n)
	}
}
