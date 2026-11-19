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
					Unpredictable: true, Vouches: []string{"err"}, Calls: []token.Position{at("a.go", 10)},
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
					Runs:  []string{"x", "less"},
					Calls: []token.Position{at("other/c.go", 3)},
				},
				{
					Key: "math/rand.Intn", Reason: "Documented.", Shipped: true, File: "vego/trusted/std/math_rand.yaml", Line: 4,
					Calls: []token.Position{at("b/b.go", 9)},
				},
			},
		},
	}
	got := TrustReport(usages, "/work")
	want := `vego trust report

Every proof vego reports as successful holds only if the contracts below are true.
None of them is checked against the code of the function it describes.

Project contracts in use: 3
  example.com/app.load  [may fail unpredictably]
    reason:  Reads a file.
    vouches for the errors and function values in: err
    defined: vego-trusted.yaml:4
    used at: a.go:10, b/b.go:7
  sort.Ints
    reason:  Another module's override.
    runs code held by: x, less
    defined: other/vego-trusted.yaml:4
    used at: other/c.go:3
  sort.Ints
    reason:  Project override.
    defined: vego-trusted.yaml:9
    used at: a.go:20

Shipped contracts in use: 1
  math/rand.Intn
    reason:  Documented.
    defined: vego/trusted/std/math_rand.yaml:4
    used at: b/b.go:9

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
