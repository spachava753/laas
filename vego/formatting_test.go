package vego

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"log"
	"math/rand"
	"os"
	"strings"
	"testing"
)

// probeCalls counts the calls of the methods of fmtProbe.
var probeCalls int

// fmtProbe has every method fmt calls, all of them on the pointer, so its
// own method set is empty and vego counts it as plain.
type fmtProbe struct{ n int }

func (p *fmtProbe) String() string                { probeCalls++; return "probe" }
func (p *fmtProbe) Error() string                 { probeCalls++; return "probe" }
func (p *fmtProbe) GoString() string              { probeCalls++; return "probe" }
func (p *fmtProbe) Format(f fmt.State, verb rune) { probeCalls++ }

// withProbes holds probes in exported and unexported fields.
type withProbes struct {
	Exported fmtProbe
	hidden   fmtProbe
	N        int
	S        string
}

// probeNest holds probes at every depth the plain rule allows.
type probeNest struct {
	W   withProbes
	Ws  []withProbes
	Wss [][]withProbes
}

// probeName is a named string type without methods.
type probeName string

// probeFormat returns a format of every verb and form the reviewers tried
// against fmt, with operands too few or too many.
func probeFormat(rng *rand.Rand) string {
	parts := []string{"%v", "%+v", "%#v", "%s", "%x", "%X", "%q", "%d", "%T", "%p", "%w", "%z", "%[1]v %[1]s", "%6.2v", "% x", "%-8q",
		"%[2]d", "%*d", "%.*s", "%!", "%", "%%", "text "}
	var b strings.Builder
	for range rng.Intn(6) {
		b.WriteString(parts[rng.Intn(len(parts))])
	}
	return b.String()
}

// TestPlainFormatting checks what the rule for formatting claims of package
// fmt, on which the shipped entries with formats and fmt.Errorf rest:
// formatting a value of a type that the rule calls plain runs none of the
// methods fmt calls, also when the type holds, at any depth, a type whose
// pointer has them all, whatever the verbs, the indices, and the number of
// operands. Every function shipped with formats is run.
func TestPlainFormatting(t *testing.T) {
	scratch = t.TempDir()
	// Values of every shape the rule calls plain, each of which holds a
	// probe or is a named type, and errors of known origin.
	operands := []any{
		0, -1, 1 << 62, uint8(200), true, 2.5, "", "text", "\xff\x00", []byte("hi"), []int{1, 2}, []string{"a", ""},
		fmtProbe{3}, withProbes{N: 1, S: "s"}, []withProbes{{N: 2}}, [][]withProbes{{{N: 3}}, nil},
		probeNest{Ws: []withProbes{{}}, Wss: [][]withProbes{{{}}}},
		probeName("x"), []probeName{"a", "b"}, struct {
			A int
			B string
		}{1, "x"},
		nil, errors.New("made"), fmt.Errorf("wrapped: %w", io.EOF),
	}
	// A logger whose output is io.Discard formats nothing, so it writes
	// to a buffer.
	logger := log.New(&bytes.Buffer{}, "p ", log.Lshortfile)
	stdout, err := os.CreateTemp(scratch, "stdout")
	if err != nil {
		t.Fatal(err)
	}
	defer func() { _ = stdout.Close() }()
	saved := os.Stdout
	os.Stdout = stdout
	defer func() { os.Stdout = saved }()
	savedLog := log.Writer()
	log.SetOutput(&bytes.Buffer{})
	defer log.SetOutput(savedLog)
	calls := map[string]func(format string, a []any){
		"fmt.Sprintf":           func(format string, a []any) { _ = fmt.Sprintf(format, a...) },
		"fmt.Sprint":            func(_ string, a []any) { _ = fmt.Sprint(a...) },
		"fmt.Sprintln":          func(_ string, a []any) { _ = fmt.Sprintln(a...) },
		"fmt.Errorf":            func(format string, a []any) { _ = fmt.Errorf(format, a...) },
		"fmt.Fprintf":           func(format string, a []any) { _, _ = fmt.Fprintf(&bytes.Buffer{}, format, a...) },
		"fmt.Fprint":            func(_ string, a []any) { _, _ = fmt.Fprint(&bytes.Buffer{}, a...) },
		"fmt.Fprintln":          func(_ string, a []any) { _, _ = fmt.Fprintln(&bytes.Buffer{}, a...) },
		"fmt.Printf":            func(format string, a []any) { _, _ = fmt.Printf(format, a...) },
		"fmt.Print":             func(_ string, a []any) { _, _ = fmt.Print(a...) },
		"fmt.Println":           func(_ string, a []any) { _, _ = fmt.Println(a...) },
		"log.Printf":            func(format string, a []any) { log.Printf(format, a...) },
		"log.Print":             func(_ string, a []any) { log.Print(a...) },
		"log.Println":           func(_ string, a []any) { log.Println(a...) },
		"(*log.Logger).Printf":  func(format string, a []any) { logger.Printf(format, a...) },
		"(*log.Logger).Print":   func(_ string, a []any) { logger.Print(a...) },
		"(*log.Logger).Println": func(_ string, a []any) { logger.Println(a...) },
	}
	rng := rand.New(rand.NewSource(1))
	for range 3000 {
		format := probeFormat(rng)
		a := make([]any, rng.Intn(4))
		for i := range a {
			a[i] = operands[rng.Intn(len(operands))]
		}
		for name, call := range calls {
			probeCalls = 0
			call(format, a)
			if probeCalls != 0 {
				t.Fatalf("%s(%q, %#v) ran %d methods of a probe", name, format, a, probeCalls)
			}
		}
	}
}
