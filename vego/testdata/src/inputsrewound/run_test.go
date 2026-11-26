package inputsrewound

import (
	"os"
	"path/filepath"
	"testing"
)

// TestProvedLoopsDoNotEnd runs the functions whose loops vego proves to end
// on the false entry of rewindFile: each reads a file of a few bytes and
// rewinds it after every read, so it would run for ever, and stops only at
// rewindFile's panic.
func TestProvedLoopsDoNotEnd(t *testing.T) {
	name := filepath.Join(t.TempDir(), "f.txt")
	if err := os.WriteFile(name, []byte("abc"), 0o600); err != nil {
		t.Fatal(err)
	}
	for _, run := range []struct {
		name string
		f    func(string)
	}{{"RewoundTwo", RewoundTwo}, {"Outer", Outer}} {
		rewound = 0
		func() {
			defer func() {
				if recover() != errEndless {
					t.Errorf("%s ended, which the false entry should keep it from doing", run.name)
				}
			}()
			run.f(name)
		}()
	}
}
