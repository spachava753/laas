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
	const counted = `; echo '(:rlimit 7)'`
	answer := `echo unsat; echo '(:reason-unknown "")'` + counted
	tests := []struct {
		name, reply string
		want        Result // checked when fault is false
		fault       bool
	}{
		{"an answer", answer, Proved, false},
		{"an error before the answer", `echo '(error "line 1: unknown constant")'; ` + answer, 0, true},
		{"a line after the answer", `echo unsat; echo '(:reason-unknown "")'; echo extra` + counted, 0, true},
		{"no count of resources", `echo unsat; echo '(:reason-unknown "")'`, 0, true},
		{"a count that is not one", `echo unsat; echo '(:reason-unknown "")'; echo '(:rlimit many)'`, 0, true},
		{"no reason", `echo unsat` + counted, 0, true},
		{"another word", `echo valid; echo '(:reason-unknown "")'` + counted, 0, true},
		{"a process that ends", `exit 3`, 0, true},
		{"a reason that is a limit", `echo unknown; echo '(:reason-unknown "max. resource limit exceeded")'` + counted, Exhausted, false},
		{"a tactic out of the limit", `echo '(error "tactic failed: max. resource limit exceeded")'; echo '(:reason-unknown "max. resource limit exceeded")'` + counted, Exhausted, false},
		{"a tactic that fails otherwise", `echo '(error "tactic failed: something")'; echo '(:reason-unknown "max. resource limit exceeded")'` + counted, 0, true},
		{"another reason", `echo unknown; echo '(:reason-unknown "(incomplete quantifiers)")'` + counted, Unknown, false},
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
		{Op: logic.OpIs, Sort: logic.Bool, Args: []*logic.Term{x, logic.NilErr()}},
		{Op: logic.OpIs, Sort: logic.Bool, Args: []*logic.Term{logic.NilErr()}},
		{Op: logic.OpIs, Sort: logic.Int, Args: []*logic.Term{logic.NilErr(), logic.NilErr()}},
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

// TestCache checks that an answer is read from the cache only for the same
// text with the same names asked, and that an answer that depends on the
// machine is asked again.
func TestCache(t *testing.T) {
	x := logic.Const("x", logic.Int)
	goal := logic.Lt(x, x)
	const counted = `; echo '(:rlimit 7)'`
	// counting returns a solver whose fake Z3 gives the reply, and a
	// function that reports how many problems it was asked.
	counting := func(t *testing.T, reply string) (*Solver, func() int) {
		file := filepath.Join(t.TempDir(), "asked")
		s, err := New(fake(t, pinned, "echo x >> "+file+"; "+reply))
		if err != nil {
			t.Fatal(err)
		}
		return s, func() int {
			content, _ := os.ReadFile(file)
			return strings.Count(string(content), "x")
		}
	}
	var costs []Cost
	observed := Options{Observe: func(c Cost) { costs = append(costs, c) }}
	t.Run("the same problem", func(t *testing.T) {
		s, asked := counting(t, `echo unsat; echo '(:reason-unknown "")'`+counted)
		costs = nil
		for range 3 {
			if got := s.Prove(nil, goal, observed); got != Proved {
				t.Fatalf("got %v, want proved", got)
			}
		}
		if asked() != 1 {
			t.Fatalf("Z3 was asked %d times, want once", asked())
		}
		if len(costs) != 3 || costs[0].Cached || !costs[1].Cached || !costs[2].Cached || costs[1].Effort != 7 || costs[1].Bytes != costs[0].Bytes {
			t.Fatalf("costs %+v, want the first solved and the others cached with its count", costs)
		}
	})
	t.Run("an unknown when canceled", func(t *testing.T) {
		s, asked := counting(t, `echo unknown; echo '(:reason-unknown "canceled")'`+counted)
		for range 2 {
			if got := s.Prove(nil, goal, Options{}); got != Exhausted {
				t.Fatalf("got %v, want exhausted", got)
			}
		}
		if asked() != 1 {
			t.Fatalf("Z3 was asked %d times, want once", asked())
		}
	})
	t.Run("another resource limit", func(t *testing.T) {
		s, asked := counting(t, `echo unknown; echo '(:reason-unknown "max. resource limit exceeded")'`+counted)
		for _, effort := range []int{1000, 2000, 1000} {
			if got := s.Prove(nil, goal, Options{Effort: effort}); got != Exhausted {
				t.Fatalf("got %v, want exhausted", got)
			}
		}
		if asked() != 2 {
			t.Fatalf("Z3 was asked %d times, want twice", asked())
		}
	})
	t.Run("other names asked", func(t *testing.T) {
		s, asked := counting(t, `echo unsat; echo '(:reason-unknown "")'`+counted)
		y := logic.Const("y", logic.Int)
		facts := []*logic.Term{logic.Lt(x, y), logic.Lt(y, x)}
		s.Model(facts, Options{}, []*logic.Term{x})
		s.Model(facts, Options{}, []*logic.Term{y})
		s.Model(facts, Options{}, []*logic.Term{x})
		if asked() != 2 {
			t.Fatalf("Z3 was asked %d times, want twice", asked())
		}
	})
	for _, test := range []struct{ name, reply string }{
		{"an unknown for want of memory", `echo unknown; echo '(:reason-unknown "memout")'` + counted},
		{"a process out of memory", `echo '(error "out of memory")' >&2; exit 101`},
	} {
		t.Run(test.name, func(t *testing.T) {
			s, asked := counting(t, test.reply)
			s.Prove(nil, goal, Options{})
			s.Prove(nil, goal, Options{})
			if asked() != 2 {
				t.Fatalf("Z3 was asked %d times, want twice", asked())
			}
		})
	}
	t.Run("a late answer", func(t *testing.T) {
		saved := wallLimit
		wallLimit = 200 * time.Millisecond
		defer func() { wallLimit = saved }()
		s, asked := counting(t, `sleep 1; echo unsat; echo '(:reason-unknown "")'`+counted)
		for range 2 {
			if got := s.Prove(nil, goal, Options{}); got != Timeout {
				t.Fatalf("got %v, want %v", got, Timeout)
			}
		}
		if asked() != 2 {
			t.Fatalf("Z3 was asked %d times, want twice", asked())
		}
	})
	t.Run("two binaries", func(t *testing.T) {
		proving, _ := counting(t, `echo unsat; echo '(:reason-unknown "")'`+counted)
		refuting, _ := counting(t, `echo sat; echo '(:reason-unknown "")'`+counted)
		if proving.Prove(nil, goal, Options{}) != Proved || refuting.Prove(nil, goal, Options{}) != Refuted {
			t.Fatal("one binary answered with what another said")
		}
	})
	// The comments that name the terms of the logic are not sent, so two
	// problems that differ only in the names are one text, asked once; a
	// fault still saves the names for a person to read.
	t.Run("texts that differ only in the comments", func(t *testing.T) {
		s, asked := counting(t, `echo unsat; echo '(:reason-unknown "")'`+counted)
		costs = nil
		for _, name := range []string{"a", "a much longer name"} {
			c := logic.Const(name, logic.Int)
			if strings.Contains(Script([]*logic.Term{logic.Not(logic.Lt(c, c))}, Options{}), ";") {
				t.Fatalf("the text sent to Z3 has a comment")
			}
			s.Prove(nil, logic.Lt(c, c), observed)
		}
		if asked() != 1 || len(costs) != 2 || costs[0].Bytes != costs[1].Bytes || !costs[1].Cached {
			t.Fatalf("Z3 was asked %d times, with costs %+v; want one problem asked once, the second answer from the cache with the same bytes", asked(), costs)
		}
		broken, err := New(fake(t, pinned, "exit 3"))
		if err != nil {
			t.Fatal(err)
		}
		func() {
			defer func() {
				fault, _ := recover().(*Fault)
				if fault == nil {
					t.Fatal("a process that ends is not a fault")
				}
				saved, err := os.ReadFile(fault.File)
				if err != nil || !strings.Contains(string(saved), "; a much longer name") {
					t.Errorf("the problem saved for the fault does not name the constant: %q, %v", saved, err)
				}
			}()
			c := logic.Const("a much longer name", logic.Int)
			broken.Prove(nil, logic.Lt(c, c), Options{})
		}()
	})
	t.Run("the oldest are forgotten", func(t *testing.T) {
		s, asked := counting(t, `echo unsat; echo '(:reason-unknown "")'`+counted)
		saved := cacheBytes
		cacheBytes = len(Script([]*logic.Term{logic.Not(goal)}, Options{})) + 10
		defer func() { cacheBytes = saved }()
		other := logic.Lt(x, logic.IntLit(0))
		if len(Script([]*logic.Term{logic.Not(other)}, Options{})) > cacheBytes {
			t.Fatal("the other problem is too long to be kept")
		}
		s.Prove(nil, goal, Options{})
		s.Prove(nil, other, Options{})
		s.Prove(nil, goal, Options{})
		if asked() != 3 {
			t.Fatalf("Z3 was asked %d times, want three times", asked())
		}
	})
	t.Run("Z3", func(t *testing.T) {
		z3 := solverFor(t)
		costs = nil
		y := logic.Const("cache y", logic.Int)
		first := z3.Prove([]*logic.Term{logic.Lt(x, y)}, logic.Le(x, y), observed)
		again := z3.Prove([]*logic.Term{logic.Lt(x, y)}, logic.Le(x, y), observed)
		if first != Proved || again != Proved || len(costs) != 2 || !costs[1].Cached || costs[0].Cached || costs[0].Effort <= 0 || costs[1].Effort != costs[0].Effort {
			t.Fatalf("got %v and %v with costs %+v, want proved twice, the second from the cache with the same count", first, again, costs)
		}
	})
}
