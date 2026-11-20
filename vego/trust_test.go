package vego

import (
	"go/token"
	"go/types"
	"path/filepath"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/analysis"
)

func TestParseTrustFile(t *testing.T) {
	tests := []struct {
		name    string
		content string
		want    string // a fragment of the reported problem, or empty for a valid file
	}{
		{"accepts a complete entry", `
version: 1
trusted:
  sort.Ints:
    reason: Documented.
    modifies: [x]
    requires: ["|x| >= 0"]
    ensures: ["|x'| = |x|"]
`, ""},
		{"accepts an entry that writes nothing", "version: 1\ntrusted:\n  os.Getpid:\n    reason: Documented.\n    modifies: []\n", ""},
		{"requires a modifies list", "version: 1\ntrusted:\n  os.Getpid:\n    reason: Documented.\n", "needs a modifies list"},
		{"requires a version", "trusted: {}\n", `missing "version: 1"`},
		{"rejects another version", "version: 2\ntrusted: {}\n", "unsupported version"},
		{"requires a reason", "version: 1\ntrusted:\n  os.Getpid:\n    ensures: [\"result >= 0\"]\n", "needs a reason"},
		{"rejects an empty reason", "version: 1\ntrusted:\n  os.Getpid:\n    reason: \"  \"\n", "needs a reason"},
		{"rejects an unknown field", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n    ensure: [\"result >= 0\"]\n", `unknown field "ensure"`},
		{"rejects an unknown top-level key", "version: 1\ntrust: {}\n", `unknown key "trust"`},
		{"rejects a formula that does not parse", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n    ensures: [\"result >=\"]\n", "syntax error in ensures"},
		{"rejects a formula that is not a list", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n    ensures: \"result >= 0\"\n", "must be a list"},
		{"rejects duplicate entries", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n  os.Getpid:\n    reason: r\n", "occurs more than once"},
		{"rejects a repeated field", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n    requires: [\"x != 0\"]\n    requires: []\n", "occurs more than once"},
		{"rejects an alias as a reason", "version: 1\ntrusted:\n  os.Getpid:\n    requires: &empty []\n    reason: *empty\n", "aliases are not supported"},
		{"rejects a reason that is not text", "version: 1\ntrusted:\n  os.Getpid:\n    reason: [a, b]\n", "must be text"},
		{"rejects a second document", "version: 1\ntrusted: {}\n---\nversion: 1\ntrusted: {}\n", "exactly one YAML document"},
		{"accepts a list of error results it vouches for", "version: 1\ntrusted:\n  os.Remove:\n    reason: r\n    modifies: []\n    vouches: [result]\n", ""},
		{"rejects vouches that is not a list", "version: 1\ntrusted:\n  os.Remove:\n    reason: r\n    modifies: []\n    vouches: result\n", "vouches of os.Remove must be a list"},
		{"accepts a function parameter with a contract", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    runs: [f]\n    calls:\n      f(i):\n        requires: [\"0 <= i < n\"]\n    modifies: []\n", ""},
		{"shows each clause of calls apart in the report", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    runs: [f]\n    calls:\n      f(i):\n        requires: [\"i < 0 Or i > n\", \"i = 0\"]\n    modifies: []\n", ""},
		{"accepts a function that must be deterministic", "version: 1\ntrusted:\n  strings.FieldsFunc:\n    reason: r\n    runs: [f]\n    calls:\n      f(c):\n        deterministic: true\n    modifies: []\n", ""},
		{"rejects deterministic that is not true or false", "version: 1\ntrusted:\n  strings.FieldsFunc:\n    reason: r\n    runs: [f]\n    calls:\n      f(c):\n        deterministic: yes\n    modifies: []\n", "deterministic under f(c) in the calls of strings.FieldsFunc must be true or false"},
		{"accepts a contract with nothing in it", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    runs: [f]\n    calls:\n      f(i): {}\n    modifies: []\n", ""},
		{"rejects calls that is not a mapping", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    calls: [f]\n    modifies: []\n", "calls of sort.Search must map"},
		{"rejects a key without parameters", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    calls:\n      f: {}\n    modifies: []\n", `"f" must name a function parameter and its parameters`},
		{"rejects a key that is not names", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    calls:\n      f(i + 1): {}\n    modifies: []\n", "must name a function parameter"},
		{"rejects a contract that is not a mapping", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    calls:\n      f(i):\n    modifies: []\n", "f(i) must be a mapping"},
		{"rejects an unknown field of a contract", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    calls:\n      f(i):\n        ensures: []\n    modifies: []\n", `unknown field "ensures" under f(i) in the calls of sort.Search; expected requires or deterministic`},
		{"rejects calls requires that do not parse", "version: 1\ntrusted:\n  sort.Search:\n    reason: r\n    calls:\n      f(i):\n        requires: [\"i <\"]\n    modifies: []\n", "syntax error in requires of f(i) in calls"},
		{"accepts what a function keeps", "version: 1\ntrusted:\n  bufio.NewScanner:\n    reason: r\n    keeps:\n      r: [result]\n    modifies: []\n", ""},
		{"rejects keeps that is not a mapping", "version: 1\ntrusted:\n  bufio.NewScanner:\n    reason: r\n    keeps: [r]\n    modifies: []\n", "keeps of bufio.NewScanner must map a parameter"},
		{"rejects a destination that is not a list", "version: 1\ntrusted:\n  bufio.NewScanner:\n    reason: r\n    keeps:\n      r: result\n    modifies: []\n", "r must map to a list of results and parameters"},
		{"rejects a destination that is not a name", "version: 1\ntrusted:\n  bufio.NewScanner:\n    reason: r\n    keeps:\n      r: [[result]]\n    modifies: []\n", "r must map to a list of names"},
		{"rejects a parameter kept twice", "version: 1\ntrusted:\n  io.TeeReader:\n    reason: r\n    keeps:\n      r: [result]\n      r: [result]\n    modifies: []\n", "occurs more than once"},
		{"explains an unquoted formula", "version: 1\ntrusted:\n  sort.Ints:\n    reason: r\n    ensures:\n      - Forall i in [0, |x|) : x'[i] >= 0\n", "must be quoted"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			file := parseTrustFile("vego-trusted.yaml", []byte(test.content), false)
			var problems []string
			for _, problem := range file.problems {
				problems = append(problems, problem.msg)
			}
			switch {
			case test.want == "" && len(problems) > 0:
				t.Fatalf("unexpected problems: %v", problems)
			case test.want != "" && !strings.Contains(strings.Join(problems, "\n"), test.want):
				t.Fatalf("problems %v do not mention %q", problems, test.want)
			}
		})
	}
}

func TestUnreadableTrustFile(t *testing.T) {
	// A directory where the file should be exists but cannot be read as one.
	file := loadTrustFile(t.TempDir())
	if file == nil || len(file.problems) != 1 || !strings.Contains(file.problems[0].msg, "cannot read the trust file") {
		t.Fatalf("an unreadable trust file must be a reported problem, got %+v", file)
	}
	if missing := loadTrustFile(filepath.Join(t.TempDir(), TrustFileName)); missing != nil {
		t.Fatalf("a missing trust file is no file, got %+v", missing)
	}
}

func TestReport(t *testing.T) {
	at := func(file string, line int) token.Position {
		return token.Position{Filename: "/work/" + file, Line: line}
	}
	projectKeys := map[string][]string{
		"/work/vego-trusted.yaml": {"example.com/app.load", "example.com/app.unused", "sort.Ints"},
	}
	usages := []*Usage{
		{
			ProjectKeys: projectKeys,
			Entries: []*EntryUse{
				{
					Key: "example.com/app.load", Reason: "Reads a file.", File: "/work/vego-trusted.yaml", Line: 4,
					Unpredictable: true, Vouches: []string{"err"}, Keeps: []string{"r in result and w"}, Calls: []token.Position{at("a.go", 10)},
				},
				{
					Key: "sort.Ints", Reason: "Project override.", File: "/work/vego-trusted.yaml", Line: 9,
					Calls: []token.Position{at("a.go", 20)},
				},
			},
			Constructors: []token.Position{at("a.go", 30)},
		},
		nil,
		{
			ProjectKeys: map[string][]string{"/work/other/vego-trusted.yaml": {"sort.Ints"}},
			Entries: []*EntryUse{
				{
					Key: "example.com/app.load", Reason: "Reads a file.", File: "/work/vego-trusted.yaml", Line: 4,
					Calls: []token.Position{at("b/b.go", 7)},
				},
				{
					Key: "sort.Ints", Reason: "Another module's override.", File: "/work/other/vego-trusted.yaml", Line: 4,
					Runs:      []string{"x", "less"},
					Callbacks: []string{"less(i, j) when: 0 <= i < |x| Or i = 0; 0 <= j < |x|"},
					Calls:     []token.Position{at("other/c.go", 3)},
				},
				{
					Key: "math/rand.Intn", Reason: "Documented.", Shipped: true, File: "vego/trusted/std/math_rand.yaml", Line: 4,
					Calls: []token.Position{at("b/b.go", 9)},
				},
				{
					Key: "(*sync.Mutex).Lock", Reason: "Documented.", Shipped: true, File: "vego/trusted/std/sync.yaml", Line: 9,
					Calls: []token.Position{at("a.go", 40)}, States: []string{"sync.Mutex held: True when locked."},
				},
				{
					Key: "(*sync.Mutex).Unlock", Reason: "Documented.", Shipped: true, File: "vego/trusted/std/sync.yaml", Line: 19,
					Calls: []token.Position{at("a.go", 41)}, States: []string{"sync.Mutex held: True when locked."},
				},
				{
					Key: "(example.com/lib.Sink).Put", Reason: "Every sink takes a number.", File: "/work/vego-trusted.yaml", Line: 12,
					Every: "example.com/lib.Sink", Relied: []string{"example.com/app"}, Calls: []token.Position{at("b/b.go", 11)},
				},
				{
					Key: "example.com/lib.Hook", Reason: "Hooks write nothing.", File: "/work/vego-trusted.yaml", Line: 16,
					Every: "example.com/lib.Hook", Relied: []string{"example.com/app/b", "example.com/app"},
				},
			},
		},
	}
	got := TrustReport(usages, "/work")
	want := `vego trust report

Every proof vego reports as successful holds only if the contracts below are true.
None of them is checked against the code of the function it describes.

Project contracts in use: 5
  (example.com/lib.Sink).Put
    reason:  Every sink takes a number.
    a claim about Put of every value of example.com/lib.Sink, or of an interface that has Put from it, that verified code gets from code that is not verified: from a caller, directly or in memory an argument reaches, or from a call through a value; a value that a trusted function returns or writes is claimed by that function's vouches
    defined: vego-trusted.yaml:12
    used at: b/b.go:11
  example.com/app.load  [may fail unpredictably]
    reason:  Reads a file.
    keeps code held by: r in result and w; a claim that the function runs none of it while the call lasts unless runs lists it, holds it afterwards only in what it is kept in, and starts or registers nothing that runs it later
    vouches for the errors and function values in: err
    defined: vego-trusted.yaml:4
    used at: a.go:10, b/b.go:7
  example.com/lib.Hook
    reason:  Hooks write nothing.
    a claim about every value of example.com/lib.Hook that verified code gets from code that is not verified: from a caller, directly or in memory an argument reaches, or from a call through a value; a value that a trusted function returns or writes is claimed by that function's vouches
    defined: vego-trusted.yaml:16
    relied on in: example.com/app, example.com/app/b
  sort.Ints
    reason:  Another module's override.
    runs code held by: x, less
    calls less(i, j) when: 0 <= i < |x| Or i = 0; 0 <= j < |x|
    defined: other/vego-trusted.yaml:4
    used at: other/c.go:3
  sort.Ints
    reason:  Project override.
    defined: vego-trusted.yaml:9
    used at: a.go:20

Shipped contracts in use: 3
  (*sync.Mutex).Lock
    reason:  Documented.
    defined: vego/trusted/std/sync.yaml:9
    used at: a.go:40
  (*sync.Mutex).Unlock
    reason:  Documented.
    defined: vego/trusted/std/sync.yaml:19
    used at: a.go:41
  math/rand.Intn
    reason:  Documented.
    defined: vego/trusted/std/math_rand.yaml:4
    used at: b/b.go:9

States the contracts in use speak of: 1
  Each is about the goroutine that runs a verified function. A proof that reads one holds only if no other
  goroutine writes the memory the function uses while it runs, also while it waits in Lock, RLock, or Do,
  except to lock and unlock a mutex this goroutine does not hold or to call Do on a Once this goroutine is not
  inside Do on (what the function handed to that Do writes is not excepted); if nobody unlocks a mutex this
  goroutine holds; and if every call that waits for another goroutine returns.
  sync.Mutex held
    means:   True when locked.

Project contracts no proof uses: 1
  example.com/app.unused  (vego-trusted.yaml)

Built-in: errors.New and fmt.Errorf return a non-nil error.
    used at: a.go:30
`
	if got != want {
		t.Fatalf("report differs\ngot:\n%s\nwant:\n%s", got, want)
	}
}

// TestSampleRanges checks that a value Z3 proposes for a sample outside the
// range of its type is refused, so that a model is never taken for an input.
func TestSampleRanges(t *testing.T) {
	pass := &analysis.Pass{TypesSizes: types.SizesFor("gc", "amd64")}
	v := &fnVerifier{pkgVerifier: &pkgVerifier{pass: pass}}
	b := &sampler{v: v}
	c := b.number(types.Typ[types.Uint8])
	for value, want := range map[int64]bool{0: true, 255: true, 300: false, -1: false} {
		if got := rangesHold(b.facts, map[string]*logic.Term{c.Name: logic.IntLit(value)}); got != want {
			t.Errorf("rangesHold for a byte of %d = %t, want %t", value, got, want)
		}
	}
}

// TestOfferChecksRanges checks that a sample whose values Z3 proposed out
// of the range of their type never reaches accept, and that one in range
// does.
func TestOfferChecksRanges(t *testing.T) {
	pass := &analysis.Pass{TypesSizes: types.SizesFor("gc", "amd64")}
	v := &fnVerifier{pkgVerifier: &pkgVerifier{pass: pass}}
	b := &sampler{v: v}
	c := b.number(types.Typ[types.Uint8])
	input := &witness{consts: map[string]*logic.Term{"$x": c}, memo: map[*logic.Term]*logic.Term{}}
	for value, want := range map[int64]bool{7: true, 300: false} {
		called := false
		offer(b, input, solver.Unknown, map[string]*logic.Term{c.Name: logic.IntLit(value)}, func(*witness) bool {
			called = true
			return true
		})
		if called != want {
			t.Errorf("accept called for a byte of %d: %t, want %t", value, called, want)
		}
	}
	defer func() {
		if _, ok := recover().(*solver.Fault); !ok {
			t.Error("a value out of range after sat is not a fault")
		}
	}()
	offer(b, input, solver.Refuted, map[string]*logic.Term{c.Name: logic.IntLit(300)}, func(*witness) bool { return true })
}
