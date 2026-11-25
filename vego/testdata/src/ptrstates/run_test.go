package ptrstates

import (
	"io"
	"os"
	"path/filepath"
	"testing"
)

// TestRefusedWouldFail shows that what the refused programs claimed was
// false: each returns a value whose Close says it was closed already, and
// a copy of a file shares what it refers to.
func TestRefusedWouldFail(t *testing.T) {
	for name, fn := range map[string]func(string) (io.Closer, error){
		"FileClosedThenReturned": FileClosedThenReturned, "ClosedBeforeConversion": ClosedBeforeConversion,
		"TwoConversions": TwoConversions, "CopyAfterClose": CopyAfterClose,
	} {
		file := filepath.Join(t.TempDir(), "f")
		if err := os.WriteFile(file, []byte("x"), 0o600); err != nil {
			t.Fatal(err)
		}
		c, err := fn(file)
		if err != nil {
			t.Fatal(err)
		}
		if err := c.Close(); err == nil {
			t.Errorf("%s returned a value that was not closed", name)
		}
	}
	file := filepath.Join(t.TempDir(), "f")
	if err := os.WriteFile(file, []byte("x"), 0o600); err != nil {
		t.Fatal(err)
	}
	if c, err := LoopClose(file, 2); err != nil || c.Close() == nil {
		t.Error("LoopClose returned a value that was not closed")
	}
	f, _ := os.Open(file)
	AliasClosed(f, f)
	if f.Close() == nil {
		t.Error("AliasClosed left the file open")
	}
	// The ghost state of a project closer is what calls of Close on it did.
	if c := ClosedThenReturned().(*P); c.n != 1 {
		t.Errorf("ClosedThenReturned: Close was called %d times", c.n)
	}
}

// TestClaims checks what the verified programs claim.
func TestClaims(t *testing.T) {
	file := filepath.Join(t.TempDir(), "f")
	if err := os.WriteFile(file, []byte("x"), 0o600); err != nil {
		t.Fatal(err)
	}
	c, err := OpenAndConvert(file)
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Close(); err != nil {
		t.Errorf("OpenAndConvert returned a closed file: %v", err)
	}
	if err := OpenThenClose(file); err != nil {
		t.Error(err)
	}
	f, _ := os.Open(file)
	g, _ := os.Open(file)
	OneOfTwo(f, g)
	if err := f.Close(); err == nil {
		t.Error("OneOfTwo left f open")
	}
	if err := g.Close(); err != nil {
		t.Errorf("OneOfTwo closed g: %v", err)
	}
	if p := ClosedProject().(*P); p.n != 1 {
		t.Errorf("ClosedProject: Close was called %d times", p.n)
	}
}
