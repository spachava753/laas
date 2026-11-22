package vego

import (
	"bytes"
	"errors"
	"fmt"
	"go/token"
	"go/types"
	"io"
	"log"
	"math"
	"math/big"
	"math/rand"
	"os"
	"slices"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
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

// badCalls counts the calls of methods fmt must not call on the values of
// the rule for String and Error methods.
var badCalls int

// valueString has String on the value; fmt calls it on a value and through
// a pointer that is not nil.
type valueString struct{ N int }

func (v valueString) String() string { return "value" }

// both is an error and a Stringer; fmt must call Error only.
type both struct{ N int }

func (b both) Error() string  { return "error" }
func (b both) String() string { badCalls++; return "string" }

// nilSafe has String on the pointer and answers for nil.
type nilSafe struct{ N int }

func (p *nilSafe) String() string {
	if p == nil {
		return "nil"
	}
	return "safe"
}

// nilPanics has String on the pointer and panics for nil.
type nilPanics struct{ N int }

func (p *nilPanics) String() string { return strings.Repeat("x", p.N) }

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
// operands; and of a value with a String or Error method, fmt calls only
// that method, and Error for a value that has both. Every function shipped
// with formats is run.
func TestPlainFormatting(t *testing.T) {
	alone(t)
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
		// Values whose String or Error method the rule checks.
		valueString{1}, &valueString{2}, (*valueString)(nil), both{3}, &both{4}, &nilSafe{5}, (*nilSafe)(nil), &nilPanics{6}, (*nilPanics)(nil),
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
			probeCalls, badCalls = 0, 0
			call(format, a)
			if probeCalls != 0 {
				t.Fatalf("%s(%q, %#v) ran %d methods of a probe", name, format, a, probeCalls)
			}
			if badCalls != 0 {
				t.Fatalf("%s(%q, %#v) called String on an error", name, format, a)
			}
		}
	}
}

// boundCase is one operand of TestFormatBound: the Go value, its type for
// the bound, its value in the logic, and what fmt prints of the parts the
// logic has no terms for, which the guide assumes.
type boundCase struct {
	value   any
	t       types.Type
	val     value
	assumed func(verbs []string) int
	// pointer is set when value is a pointer to a struct, and t and val
	// are what it points to.
	pointer bool
}

// pair is a struct of the kind the bound reads field by field.
type pair struct {
	A int
	B string
}

// boundCases returns operands at the extremes of what fmt prints for them.
func boundCases() []boundCase {
	pkg := types.NewPackage("github.com/spachava753/laas/vego", "vego")
	pairType := types.NewNamed(types.NewTypeName(token.NoPos, pkg, "pair", nil), types.NewStruct([]*types.Var{
		types.NewField(token.NoPos, pkg, "A", types.Typ[types.Int], false),
		types.NewField(token.NoPos, pkg, "B", types.Typ[types.String], false),
	}, nil), nil)
	none := func([]string) int { return 0 }
	scalar := func(x any, t types.Type) boundCase {
		return boundCase{x, t, value{logic.IntLit(0)}, none, false}
	}
	text := func(s string) boundCase {
		return boundCase{s, types.Typ[types.String], value{logic.Bytes(s)}, none, false}
	}
	header := func(n int) value {
		return value{logic.RefLit(1), logic.IntLit(0), logic.IntLit(int64(n)), logic.IntLit(int64(n))}
	}
	// printed measures, for what the bound has no term for, the most fmt
	// prints of it under any of the verbs.
	printed := func(x any) func(verbs []string) int {
		return func(verbs []string) int {
			most := 0
			for _, verb := range verbs {
				most = max(most, len(fmt.Sprintf(verb, x)))
			}
			return most
		}
	}
	words := []string{"\x80\x01\u0080", "", "plain"}
	pairs := []pair{{-1 << 63, "\x80\x80"}, {1, ""}}
	return []boundCase{
		scalar(math.MinInt64, types.Typ[types.Int64]),
		scalar(uint64(math.MaxUint64), types.Typ[types.Uint64]),
		scalar(uint8(255), types.Typ[types.Uint8]),
		scalar(true, types.Typ[types.Bool]),
		scalar(-math.MaxFloat64, types.Typ[types.Float64]),
		scalar(math.SmallestNonzeroFloat64, types.Typ[types.Float64]),
		scalar(float32(-math.MaxFloat32), types.Typ[types.Float32]),
		scalar(complex(-math.MaxFloat64, -math.MaxFloat64), types.Typ[types.Complex128]),
		text("\x80\x01\u0080 \U0010ffff"),
		text(strings.Repeat("\x01", 1000)),
		text(strings.Repeat("\u0080", 500)),
		text(""),
		{[]byte("\x80\x01\xff\x00"), types.NewSlice(types.Typ[types.Uint8]), header(4), none, false},
		{[]byte(strings.Repeat("\xff", 1000)), types.NewSlice(types.Typ[types.Uint8]), header(1000), none, false},
		{[]int{math.MinInt64, 0, 7}, types.NewSlice(types.Typ[types.Int]), header(3), none, false},
		{[]float64{-math.MaxFloat64, math.SmallestNonzeroFloat64}, types.NewSlice(types.Typ[types.Float64]), header(2), none, false},
		{words, types.NewSlice(types.Typ[types.String]), header(len(words)), func(verbs []string) int {
			total := 0
			for _, word := range words {
				total += printed(word)(verbs)
			}
			return total
		}, false},
		{pair{math.MinInt64, "\x80\x01"}, pairType, value{logic.IntLit(0), logic.Bytes("\x80\x01")}, none, false},
		{pairs, types.NewSlice(pairType), header(len(pairs)), func(verbs []string) int {
			total := 0
			for _, p := range pairs {
				total += printed(p.B)(verbs)
			}
			return total
		}, false},
		{nil, types.Typ[types.UntypedNil], nil, none, false},
		{&pair{math.MinInt64, strings.Repeat("\x80", 300)}, pairType, value{logic.IntLit(0), logic.Bytes(strings.Repeat("\x80", 300))}, none, true},
		{(*pair)(nil), pairType, value{logic.IntLit(0), logic.Bytes("")}, none, true},
		{errors.New("made \x80"), types.Universe.Lookup("error").Type(), value{logic.NilErr()}, printed(errors.New("made \x80")), false},
	}
}

// TestBoundOnFormatting checks the bound vego proves on what formatting
// writes against the running fmt. Each weight is checked alone, for one
// operand under one verb: what fmt writes is at most what fmtWeight counts
// for it, the width and precision included. And for formats drawn at
// random, what Sprintf writes, or Sprint and Sprintln without a format, is
// at most fmtBound plus what fmt prints of the parts that are assumed, each
// counted for every verb and once more, as the bound counts operands. The
// formats hold the widest verbs, widths and precisions up to a million and
// the largest fmt reads, indices, and stars.
func TestBoundOnFormatting(t *testing.T) {
	parallel(t)
	cases := boundCases()
	verbs := []string{"%v", "%+v", "%#v", "%s", "%q", "%+q", "%#q", "%x", "%X", "% x", "% #x", "%#x", "%d", "%b", "%#b", "%o", "%O", "%U", "%#U",
		"%c", "%e", "%E", "%f", "%F", "%g", "%G", "%t", "%T", "%p", "%w", "%z"}
	parts := append(slices.Clone(verbs), "%8.3v", "%-12q", "%.400e", "%9999.0f", "%[1]v %[1]q", "%[2]d", "%*d", "%.*s", "%!", "x ", "%")
	eval := &evaluator{bindings: map[string]*big.Int{}}
	t.Run("each verb", func(t *testing.T) {
		for _, c := range cases {
			for _, verb := range append(slices.Clone(verbs), "%8.3v", "%-12q", "%.400e", "%999999.0f", "%999999v", "% #999x") {
				out := fmt.Sprintf(verb, c.value)
				linear, _ := fmtWeight(c.val, c.t, constantSpec(verb), true, "x")
				weight := eval.number(linear.term()).Int64() + int64(c.assumed(verbs))
				if c.pointer {
					weight += fmtPointerCost
				}
				if int64(len(out)) > weight {
					t.Errorf("%s of a %s wrote %d bytes, more than its weight %d", verb, c.t, len(out), weight)
				}
			}
		}
	})
	rng := rand.New(rand.NewSource(1))
	check := func(spec fmtSpec, format string, picked []boundCase, out string) {
		t.Helper()
		ops := make([]fmtOperand, len(picked))
		assumed := 0
		uses := 1
		if !spec.line {
			uses = int(eval.number(spec.verbs).Int64()) + 1
		}
		for i, c := range picked {
			ops[i] = fmtOperand{val: c.val, t: c.t, pointer: c.pointer}
			assumed += uses * c.assumed(verbs)
		}
		size := fmtBound(spec, ops)
		term, complete := size.term(), size.complete
		if complete && assumed != 0 {
			t.Fatalf("formatting %q: the bound counts all of it, but %d bytes are assumed", format, assumed)
		}
		bound := eval.number(term).Int64() + int64(assumed)
		if int64(len(out)) > bound {
			t.Fatalf("formatting %q with %d operands wrote %d bytes, more than the bound %d", format, len(picked), len(out), bound)
		}
	}
	t.Run("formats", func(t *testing.T) {
		text := cases[slices.IndexFunc(cases, func(c boundCase) bool { s, ok := c.value.(string); return ok && len(s) == 1000 })]
		number := boundCase{999999, types.Typ[types.Int], value{logic.IntLit(0)}, func([]string) int { return 0 }, false}
		// Fixed calls first: one operand used eight times, and a width
		// taken from an operand.
		for _, fixed := range []struct {
			format string
			picked []boundCase
		}{
			{"%[1]q%[1]q%[1]q%[1]q%[1]q%[1]q%[1]q%[1]q", []boundCase{text}},
			{"%*d", []boundCase{number, number}},
			{"%10000009.10000009f", []boundCase{cases[4]}},
		} {
			a := make([]any, len(fixed.picked))
			for i, c := range fixed.picked {
				a[i] = c.value
			}
			check(constantSpec(fixed.format), fixed.format, fixed.picked, fmt.Sprintf(fixed.format, a...))
		}
		for range 2000 {
			var b strings.Builder
			for range rng.Intn(5) {
				b.WriteString(parts[rng.Intn(len(parts))])
			}
			format := b.String()
			picked := make([]boundCase, rng.Intn(4))
			a := make([]any, len(picked))
			for i := range picked {
				picked[i] = cases[rng.Intn(len(cases))]
				a[i] = picked[i].value
			}
			check(constantSpec(format), format, picked, fmt.Sprintf(format, a...))
			// The spec checkFormatAlloc gives a format that is not a
			// constant, and one without a format.
			length := logic.IntLit(int64(len(format)))
			check(fmtSpec{verbs: length, length: length, width: fmtMaxWidth, precision: fmtMaxWidth, expands: true}, format, picked, fmt.Sprintf(format, a...))
			check(fmtSpec{line: true}, "", picked, fmt.Sprintln(a...))
			check(fmtSpec{line: true}, "", picked, fmt.Sprint(a...))
		}
	})
}

// writeWatch is a writer that records whether it has been written.
type writeWatch struct{ written bool }

func (w *writeWatch) Write(p []byte) (int, error) {
	w.written = true
	return len(p), nil
}

// lateFormatted is an operand whose String method records whether the
// writer it watches was written before it was formatted.
type lateFormatted struct {
	w    *writeWatch
	late *bool
}

func (f lateFormatted) String() string {
	if f.w.written {
		*f.late = true
	}
	return "x"
}

// formatsFirst reports whether a function that formats its operands and
// writes to w formatted every operand before it wrote anything.
func formatsFirst(call func(w io.Writer, v ...any)) bool {
	w := &writeWatch{}
	late := false
	call(w, lateFormatted{w, &late}, lateFormatted{w, &late})
	return w.written && !late
}

// TestFormatsBeforeWriting holds what formats claims of a function that
// also writes or runs something its entry lists: that it formats every
// value before it writes anything its modifies lists or runs any code its
// runs lists, so that the values checked in the state of the call are the
// values formatted. Each such shipped entry has a harness here, and the
// check is seen to fail on a function that writes first.
func TestFormatsBeforeWriting(t *testing.T) {
	alone(t)
	calls := map[string]func(w io.Writer, v ...any){
		"fmt.Fprintf":           func(w io.Writer, v ...any) { fmt.Fprintf(w, "%v %v", v...) },
		"fmt.Fprint":            func(w io.Writer, v ...any) { fmt.Fprint(w, v...) },
		"fmt.Fprintln":          func(w io.Writer, v ...any) { fmt.Fprintln(w, v...) },
		"(*log.Logger).Printf":  func(w io.Writer, v ...any) { log.New(w, "p ", log.Lshortfile).Printf("%v %v", v...) },
		"(*log.Logger).Print":   func(w io.Writer, v ...any) { log.New(w, "p ", log.Lshortfile).Print(v...) },
		"(*log.Logger).Println": func(w io.Writer, v ...any) { log.New(w, "p ", log.Lshortfile).Println(v...) },
	}
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			if len(entry.formats) > 0 && (len(entry.modifies) > 0 || len(entry.runs) > 0) && calls[key] == nil {
				t.Errorf("%s formats and writes or runs what its entry lists, and no harness here checks that it formats first", key)
			}
		}
	}
	for key, call := range calls {
		if !formatsFirst(call) {
			t.Errorf("%s wrote to its writer before it had formatted every value", key)
		}
	}
	writesFirst := func(w io.Writer, v ...any) {
		_, _ = w.Write([]byte("first "))
		fmt.Fprint(w, v...)
	}
	if formatsFirst(writesFirst) {
		t.Error("a function that writes before it formats passed the check")
	}
}
