package vego

import (
	"go/token"
	"strings"
	"testing"
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
		{"accepts an entry with only a reason", "version: 1\ntrusted:\n  os.Getpid:\n    reason: Documented.\n", ""},
		{"requires a version", "trusted: {}\n", `missing "version: 1"`},
		{"rejects another version", "version: 2\ntrusted: {}\n", "unsupported version"},
		{"requires a reason", "version: 1\ntrusted:\n  os.Getpid:\n    ensures: [\"result >= 0\"]\n", "needs a reason"},
		{"rejects an empty reason", "version: 1\ntrusted:\n  os.Getpid:\n    reason: \"  \"\n", "needs a reason"},
		{"rejects an unknown field", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n    ensure: [\"result >= 0\"]\n", `unknown field "ensure"`},
		{"rejects an unknown top-level key", "version: 1\ntrust: {}\n", `unknown key "trust"`},
		{"rejects a formula that does not parse", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n    ensures: [\"result >=\"]\n", "syntax error in ensures"},
		{"rejects a formula that is not a list", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n    ensures: \"result >= 0\"\n", "must be a list"},
		{"rejects duplicate entries", "version: 1\ntrusted:\n  os.Getpid:\n    reason: r\n  os.Getpid:\n    reason: r\n", "more than one entry"},
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

func TestReport(t *testing.T) {
	at := func(file string, line int) token.Position {
		return token.Position{Filename: "/work/" + file, Line: line}
	}
	usages := []*Usage{
		{
			ProjectFile: "/work/vego-trusted.yaml",
			ProjectKeys: []string{"example.com/app.load", "example.com/app.unused", "sort.Ints"},
			Entries: map[string]*EntryUse{
				"example.com/app.load": {
					Key: "example.com/app.load", Reason: "Reads a file.", File: "/work/vego-trusted.yaml", Line: 4,
					Unpredictable: true, Calls: []token.Position{at("a.go", 10)},
				},
				"sort.Ints": {
					Key: "sort.Ints", Reason: "Project override.", File: "/work/vego-trusted.yaml", Line: 9,
					Calls: []token.Position{at("a.go", 20)},
				},
			},
			Constructors: []token.Position{at("a.go", 30)},
		},
		nil,
		{
			ProjectFile: "/work/vego-trusted.yaml",
			ProjectKeys: []string{"example.com/app.load", "example.com/app.unused", "sort.Ints"},
			Entries: map[string]*EntryUse{
				"example.com/app.load": {
					Key: "example.com/app.load", Reason: "Reads a file.", File: "/work/vego-trusted.yaml", Line: 4,
					Calls: []token.Position{at("b/b.go", 7)},
				},
				"math/rand.Intn": {
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

Project contracts in use: 2
  example.com/app.load  [may fail unpredictably]
    reason:  Reads a file.
    defined: vego-trusted.yaml:4
    used at: a.go:10, b/b.go:7
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
