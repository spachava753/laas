package solver

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
)

// fake writes a shell script that stands in for Z3: it reports the given
// version, and answers each problem by running reply, after which it
// prints the marker that ends the reply.
func fake(t *testing.T, version, reply string) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), "z3")
	script := `#!/bin/sh
if [ "$1" = "-version" ]; then
	echo "` + version + `"
	exit 0
fi
while IFS= read -r line; do
	case "$line" in
	*'(echo "'*)
		end=${line#*\(echo \"}
		end=${end%%\"*}
		` + reply + `
		echo "$end"
		;;
	esac
done
`
	if err := os.WriteFile(path, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	return path
}

const pinned = "Z3 version " + Version + " - 64 bit - build hashcode 0"

// TestVersionPin checks that only Z3 of the pinned version is used.
func TestVersionPin(t *testing.T) {
	tests := []struct {
		name, path, want string
	}{
		{"another version", fake(t, "Z3 version 4.16.0 - 64 bit", ""), "is Z3 4.16.0"},
		{"no version", fake(t, "something else", ""), "does not say which version"},
		{"no binary", filepath.Join(t.TempDir(), "missing"), "could not be run"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			_, err := New(test.path)
			if err == nil || !strings.Contains(err.Error(), test.want) || !strings.Contains(err.Error(), "z3-"+Version) {
				t.Fatalf("New(%s) = %v, want an error saying %q and how to install Z3 %s", test.path, err, test.want, Version)
			}
			// A second package asking for the same binary is told once
			// more, briefly.
			if _, again := New(test.path); again == nil || !strings.Contains(again.Error(), "cannot be used") {
				t.Fatalf("second New(%s) = %v, want a short error", test.path, again)
			}
		})
	}
	if _, err := New(fake(t, pinned, "")); err != nil {
		t.Fatalf("the pinned version was refused: %v", err)
	}
}

// TestProtocol checks that every reply other than an answer is a fault,
// never a proof, and that a problem past the wall limit counts as not
// proved.
func TestProtocol(t *testing.T) {
	x := logic.Const("x", logic.Int)
	goal := logic.Lt(x, x)
	answer := `echo unsat; echo '(:reason-unknown "")'`
	tests := []struct {
		name, reply string
		want        Result // checked when fault is false
		fault       bool
	}{
		{"an answer", answer, Proved, false},
		{"an error before the answer", `echo '(error "line 1: unknown constant")'; ` + answer, 0, true},
		{"a line after the answer", answer + `; echo extra`, 0, true},
		{"no reason", `echo unsat`, 0, true},
		{"another word", `echo valid; echo '(:reason-unknown "")'`, 0, true},
		{"a process that ends", `exit 3`, 0, true},
		{"a reason that is a limit", `echo unknown; echo '(:reason-unknown "max. resource limit exceeded")'`, Exhausted, false},
		{"another reason", `echo unknown; echo '(:reason-unknown "(incomplete quantifiers)")'`, Unknown, false},
		{"a process out of memory", `echo '(error "out of memory")' >&2; exit 101`, OutOfMemory, false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			s, err := New(fake(t, pinned, test.reply))
			if err != nil {
				t.Fatal(err)
			}
			got, fault := func() (result Result, fault *Fault) {
				defer func() {
					if r := recover(); r != nil {
						fault = r.(*Fault)
					}
				}()
				return s.Prove(nil, goal, Options{}), nil
			}()
			switch {
			case test.fault && fault == nil:
				t.Fatalf("got %v, want a fault", got)
			case !test.fault && fault != nil:
				t.Fatalf("got fault %v, want %v", fault, test.want)
			case !test.fault && got != test.want:
				t.Fatalf("got %v, want %v", got, test.want)
			}
		})
	}
	t.Run("a late answer", func(t *testing.T) {
		saved := wallLimit
		wallLimit = 200 * time.Millisecond
		defer func() { wallLimit = saved }()
		s, err := New(fake(t, pinned, "sleep 2; "+answer))
		if err != nil {
			t.Fatal(err)
		}
		if got := s.Prove(nil, goal, Options{}); got != Timeout {
			t.Fatalf("got %v, want %v", got, Timeout)
		}
	})
}

// TestNamesCannotInject checks that a name of the logic that holds SMT-LIB
// text cannot become a command: names are replaced, and the comment that
// keeps a name readable ends at a line break.
func TestNamesCannotInject(t *testing.T) {
	z3 := solverFor(t)
	for _, name := range []string{"a\n(assert false)", "b\r(assert false)", "c|(assert false)|", "d)) (assert false) ((", "nil"} {
		x := logic.Const(name, logic.Int)
		if got := z3.Prove(nil, logic.Lt(x, x), Options{}); got == Proved {
			t.Fatalf("x < x was proved for a constant named %q", name)
		}
	}
}

// TestSortsAreChecked checks that a term whose arguments have sorts its
// operator does not take is refused instead of being passed to Z3, which
// would convert between booleans and integers.
func TestSortsAreChecked(t *testing.T) {
	z3 := solverFor(t)
	b, x := logic.Const("b", logic.Bool), logic.Const("x", logic.Int)
	for _, bad := range []*logic.Term{
		{Op: logic.OpEq, Sort: logic.Bool, Args: []*logic.Term{x, b}},
		{Op: logic.OpLe, Sort: logic.Bool, Args: []*logic.Term{b, x}},
		{Op: logic.OpAnd, Sort: logic.Bool, Args: []*logic.Term{b, x}},
		{Op: logic.OpIte, Sort: logic.Bool, Args: []*logic.Term{x, b, b}},
	} {
		func() {
			defer func() {
				if r := recover(); r == nil || !strings.Contains(r.(string), "sorts do not fit") {
					t.Fatalf("%v was not refused: %v", bad, r)
				}
			}()
			z3.Prove(nil, bad, Options{})
		}()
	}
}
