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

// boundCase is one operand of TestFormatBound: the Go value, its type for
// the bound, its value in the logic, and what fmt prints of the parts the
// logic has no terms for, which the guide assumes.
type boundCase struct {
	value   any
	t       types.Type
	val     value
	assumed func(verbs []string) int
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
		return boundCase{x, t, value{logic.IntLit(0)}, none}
	}
	text := func(s string) boundCase { return boundCase{s, types.Typ[types.String], value{logic.Bytes(s)}, none} }
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
		{[]byte("\x80\x01\xff\x00"), types.NewSlice(types.Typ[types.Uint8]), header(4), none},
		{[]byte(strings.Repeat("\xff", 1000)), types.NewSlice(types.Typ[types.Uint8]), header(1000), none},
		{[]int{math.MinInt64, 0, 7}, types.NewSlice(types.Typ[types.Int]), header(3), none},
		{[]float64{-math.MaxFloat64, math.SmallestNonzeroFloat64}, types.NewSlice(types.Typ[types.Float64]), header(2), none},
		{words, types.NewSlice(types.Typ[types.String]), header(len(words)), func(verbs []string) int {
			total := 0
			for _, word := range words {
				total += printed(word)(verbs)
			}
			return total
		}},
		{pair{math.MinInt64, "\x80\x01"}, pairType, value{logic.IntLit(0), logic.Bytes("\x80\x01")}, none},
		{pairs, types.NewSlice(pairType), header(len(pairs)), func(verbs []string) int {
			total := 0
			for _, p := range pairs {
				total += printed(p.B)(verbs)
			}
			return total
		}},
		{nil, types.Typ[types.UntypedNil], nil, none},
		{errors.New("made \x80"), types.Universe.Lookup("error").Type(), value{logic.NilErr()}, printed(errors.New("made \x80"))},
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
	cases := boundCases()
	verbs := []string{"%v", "%+v", "%#v", "%s", "%q", "%+q", "%#q", "%x", "%X", "% x", "% #x", "%#x", "%d", "%b", "%#b", "%o", "%O", "%U", "%#U",
		"%c", "%e", "%E", "%f", "%F", "%g", "%G", "%t", "%T", "%p", "%w", "%z"}
	parts := append(slices.Clone(verbs), "%8.3v", "%-12q", "%.400e", "%9999.0f", "%[1]v %[1]q", "%[2]d", "%*d", "%.*s", "%!", "x ", "%")
	eval := &evaluator{bindings: map[string]*big.Int{}}
	t.Run("each verb", func(t *testing.T) {
		for _, c := range cases {
			for _, verb := range append(slices.Clone(verbs), "%8.3v", "%-12q", "%.400e", "%999999.0f", "%999999v", "% #999x") {
				out := fmt.Sprintf(verb, c.value)
				term, _ := fmtWeight(c.val, c.t, constantSpec(verb), true)
				weight := eval.number(term).Int64() + int64(c.assumed(verbs))
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
			ops[i] = fmtOperand{val: c.val, t: c.t}
			assumed += uses * c.assumed(verbs)
		}
		term, complete := fmtBound(spec, ops)
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
		number := boundCase{999999, types.Typ[types.Int], value{logic.IntLit(0)}, func([]string) int { return 0 }}
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
