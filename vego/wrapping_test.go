package vego

import (
	"errors"
	"fmt"
	"math/rand/v2"
	"reflect"
	"strings"
	"testing"
)

// TestFormatWraps checks what formatWraps reads from a format against what
// the fmt.Errorf of the running toolchain does with it: for every operand
// that is an error, errors.Is finds it in the result exactly when
// formatWraps says the result wraps it. Formats are drawn from the forms
// that fmt reads in more than one way: flags, widths and precisions of any
// length, %% with and without a width, a % at the end, verbs that are not
// letters or not valid UTF-8, argument indexes, widths taken from
// operands, missing and extra operands, and %w on nil and on things that
// are not errors.
func TestFormatWraps(t *testing.T) {
	parallel(t)
	rng := rand.New(rand.NewPCG(7, 8))
	verbs := []string{"d", "v", "s", "w", "w", "w", "!", "é", "\xff", "x", "%", "["}
	// Most numbers are short; some are long enough to overflow.
	number := func() string {
		var b strings.Builder
		length := rng.IntN(3)
		if rng.IntN(4) == 0 {
			length = 3 + rng.IntN(8)
		}
		for range length {
			b.WriteByte(byte('0' + rng.IntN(10)))
		}
		return b.String()
	}
	known, wrapped := 0, 0
	for n := range 50000 {
		var format strings.Builder
		for range rng.IntN(4) {
			format.WriteString([]string{"", "a", ": ", "%%"}[rng.IntN(4)])
			format.WriteByte('%')
			for range rng.IntN(3) {
				format.WriteByte("#0+- "[rng.IntN(5)])
			}
			switch rng.IntN(12) {
			case 0:
				format.WriteString("[" + fmt.Sprint(rng.IntN(4)) + "]")
			case 1:
				format.WriteByte('*')
			default:
				format.WriteString(number())
			}
			if rng.IntN(4) == 0 {
				format.WriteByte('.')
				if rng.IntN(8) == 0 {
					format.WriteByte('*')
				} else {
					format.WriteString(number())
				}
			}
			format.WriteString(verbs[rng.IntN(len(verbs))])
		}
		if rng.IntN(6) == 0 {
			format.WriteByte('%')
		}
		var operands []any
		var isError []bool
		for range rng.IntN(5) {
			switch rng.IntN(5) {
			case 0, 4:
				operands, isError = append(operands, errors.New("e")), append(isError, true)
			case 1:
				operands, isError = append(operands, error(nil)), append(isError, true)
			case 2:
				operands, isError = append(operands, rng.IntN(100)), append(isError, false)
			default:
				operands, isError = append(operands, "s"), append(isError, false)
			}
		}
		text := format.String()
		result := fmt.Errorf(text, operands...)
		if result == nil {
			t.Fatalf("fmt.Errorf(%q) returned nil", text)
		}
		tree, index := formatWraps(&text, isError)
		if tree == treeUnknown {
			continue
		}
		known++
		for i, operand := range operands {
			err, ok := operand.(error)
			if !ok || err == nil {
				continue
			}
			want := tree == wrapsOperand && index == i
			if want {
				wrapped++
			}
			if got := errors.Is(result, err); got != want {
				t.Fatalf("case %d: fmt.Errorf(%q, %v): errors.Is finds operand %d: %t, but formatWraps says %v, %d",
					n, text, operands, i, got, tree, index)
			}
		}
	}
	if known < 25000 || wrapped < 1200 {
		t.Fatalf("only %d formats were read and %d wrapped operands checked; the test has lost its power", known, wrapped)
	}
	t.Logf("checked %d formats that were read, %d of them wrapping an operand", known, wrapped)
}

// TestErrorsAsModelled checks what the model of errors takes from the
// implementation of errors.New, fmt.Errorf, and errors.Is in the running
// toolchain rather than from their documentation. Each call returns a new
// pointer, so that == on it is equality and never panics; none of the
// results has an Is method; and Unwrap returns what the trees say.
func TestErrorsAsModelled(t *testing.T) {
	parallel(t)
	base := errors.New("base")
	// A %w on something that is not an error is what go vet reports, so
	// the format is not a constant here.
	onInt := "x: %w"
	made := map[string]func() error{
		"errors.New":                 func() error { return errors.New("x") },
		"fmt.Errorf without %w":      func() error { return fmt.Errorf("x %d", 1) },
		"fmt.Errorf of a plain text": func() error { return fmt.Errorf("x") },
		"fmt.Errorf with %w":         func() error { return fmt.Errorf("x: %w", base) },
		"fmt.Errorf with %w on nil":  func() error { return fmt.Errorf("x: %w", error(nil)) },
		"fmt.Errorf with %w on 1":    func() error { return fmt.Errorf(onInt, 1) },
		"fmt.Errorf with two %w":     func() error { return fmt.Errorf("x: %w %w", base, base) },
	}
	for name, make := range made {
		t.Run(name, func(t *testing.T) {
			a, b := make(), make()
			if a == nil || reflect.TypeOf(a).Kind() != reflect.Pointer {
				t.Fatalf("got %T, want a pointer", a)
			}
			if a == b {
				t.Fatal("two calls returned the same error")
			}
			if _, has := a.(interface{ Is(error) bool }); has {
				t.Fatal("the error has an Is method")
			}
			if errors.Is(a, nil) || errors.Is(nil, a) || !errors.Is(error(nil), nil) {
				t.Fatal("errors.Is with nil does not compare with nil")
			}
			if !errors.Is(a, a) || errors.Is(a, b) {
				t.Fatal("errors.Is does not find the error itself, or finds another")
			}
		})
	}
	unwrapped := map[string]struct {
		err  error
		want error
	}{
		"errors.New":                 {errors.New("x"), nil},
		"fmt.Errorf without %w":      {fmt.Errorf("x %v", base), nil},
		"fmt.Errorf of a plain text": {fmt.Errorf("x"), nil},
		"fmt.Errorf with %w":         {fmt.Errorf("x: %w", base), base},
		"fmt.Errorf with %w on nil":  {fmt.Errorf("x: %w", error(nil)), nil},
		"fmt.Errorf with %w on 1":    {fmt.Errorf(onInt, 1), nil},
	}
	for name, test := range unwrapped {
		if got := errors.Unwrap(test.err); got != test.want {
			t.Errorf("%s: Unwrap returned %v, want %v", name, got, test.want)
		}
	}
}
