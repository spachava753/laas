package vego

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"math/rand"
	"testing"
)

// printsWriters calls, by the key of a shipped entry with prints, the
// function with a writer and operands; printsReturns calls, by its key, a
// function that prints may name, with the same operands.
var printsWriters = map[string]func(w io.Writer, format string, operands []any) (int, error){
	"fmt.Fprintf": func(w io.Writer, format string, operands []any) (int, error) {
		return fmt.Fprintf(w, format, operands...)
	},
	"fmt.Fprint":   func(w io.Writer, _ string, operands []any) (int, error) { return fmt.Fprint(w, operands...) },
	"fmt.Fprintln": func(w io.Writer, _ string, operands []any) (int, error) { return fmt.Fprintln(w, operands...) },
}

var printsReturns = map[string]func(format string, operands []any) string{
	"fmt.Sprintf":  func(format string, operands []any) string { return fmt.Sprintf(format, operands...) },
	"fmt.Sprint":   func(_ string, operands []any) string { return fmt.Sprint(operands...) },
	"fmt.Sprintln": func(_ string, operands []any) string { return fmt.Sprintln(operands...) },
}

// recordingWriter records each call of its Write and returns what it is
// told to; it fails the test if any other method of it is called, as the
// claim of prints says nothing else of the writer is.
type recordingWriter struct {
	t      *testing.T
	writes [][]byte
	n      func(p []byte) int
	err    error
}

func (w *recordingWriter) Write(p []byte) (int, error) {
	w.writes = append(w.writes, bytes.Clone(p))
	return w.n(p), w.err
}

func (w *recordingWriter) WriteString(string) (int, error) {
	w.t.Fatal("WriteString of the writer was called")
	return 0, nil
}

func (w *recordingWriter) ReadFrom(io.Reader) (int64, error) {
	w.t.Fatal("ReadFrom of the writer was called")
	return 0, nil
}

func (w *recordingWriter) String() string {
	w.t.Fatal("String of the writer was called")
	return ""
}

// TestPrintsClaims holds the claim of prints against every shipped entry
// that makes it: the function calls Write of the writer exactly once, with
// exactly the bytes the function its prints names returns for the same
// operands, calls no other method of the writer, and returns what Write
// returned, whatever that is.
func TestPrintsClaims(t *testing.T) {
	parallel(t)
	found := 0
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			if len(entry.prints) == 0 {
				continue
			}
			found++
			write, ok := printsWriters[key]
			as, known := printsReturns[entry.prints[0].dests[0].text]
			if !ok || !known {
				t.Errorf("no harness calls %s or %s; add them to printsWriters and printsReturns", key, entry.prints[0].dests[0].text)
				continue
			}
			rng := rand.New(rand.NewSource(3))
			for range 2000 {
				format, operands := randomFormat(rng), randomOperands(rng)
				var returned int
				w := &recordingWriter{t: t, n: func(p []byte) int {
					returned = rng.Intn(len(p) + 1)
					return returned
				}}
				if rng.Intn(3) == 0 {
					w.err = errors.New("write failed")
				}
				n, err := write(w, format, operands)
				switch {
				case len(w.writes) != 1:
					t.Fatalf("%s called Write %d times", key, len(w.writes))
				case string(w.writes[0]) != as(format, operands):
					t.Fatalf("%s wrote %q, and %s returns %q", key, w.writes[0], entry.prints[0].dests[0].text, as(format, operands))
				case n != returned || err != w.err:
					t.Fatalf("%s returned %d, %v, and Write returned %d, %v", key, n, err, returned, w.err)
				}
			}
		}
	}
	if found != len(printsWriters) {
		t.Errorf("%d shipped entries make the claim of prints, and printsWriters has %d", found, len(printsWriters))
	}
}
