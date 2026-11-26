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
	parallel(t)
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
		{"accepts a declared memory", "version: 1\nsizes:\n  memory: 256GB\n  reason: Our servers have 64 GB.\n", ""},
		{"accepts a memory in bytes", "version: 1\nsizes:\n  memory: \"1000000\"\n  reason: r\n", ""},
		{"accepts a memory in GiB", "version: 1\nsizes:\n  memory: 64 GiB\n  reason: r\n", ""},
		{"requires a reason for sizes", "version: 1\nsizes:\n  memory: 256GB\n", "sizes must be a mapping with a memory"},
		{"requires a memory for sizes", "version: 1\nsizes:\n  reason: r\n", "sizes must be a mapping with a memory"},
		{"rejects sizes that is not a mapping", "version: 1\nsizes: true\n", "sizes must be a mapping with a memory"},
		{"rejects an empty reason for sizes", "version: 1\nsizes:\n  memory: 1GB\n  reason: \" \"\n", "sizes must be a mapping with a memory"},
		{"rejects an unknown field of sizes", "version: 1\nsizes:\n  memory: 1GB\n  bound: 4GB\n  reason: r\n", `unknown field "bound" of sizes`},
		{"rejects an unknown unit", "version: 1\nsizes:\n  memory: 1Gb\n  reason: r\n", `has the unit "Gb"`},
		{"rejects a memory that is not a number", "version: 1\nsizes:\n  memory: lots\n  reason: r\n", "must be a whole number of bytes"},
		{"rejects a fraction of a unit", "version: 1\nsizes:\n  memory: 1.5TB\n  reason: r\n", "must be a whole number of bytes"},
		{"rejects no memory", "version: 1\nsizes:\n  memory: 0GB\n  reason: r\n", "must be more than 0 bytes"},
		{"rejects sizes declared twice", "version: 1\nsizes:\n  memory: 1GB\n  reason: r\nsizes:\n  memory: 1GB\n  reason: r\n", "occurs more than once"},
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

// TestMemoryUnits checks the units of a declared memory, and that no
// shipped file may declare one, which only a project can know.
func TestMemoryUnits(t *testing.T) {
	parallel(t)
	file := parseTrustFile("vego/trusted/std/x.yaml", []byte("version: 1\nsizes:\n  memory: 1GB\n  reason: r\n"), true)
	if len(file.problems) != 1 || !strings.Contains(file.problems[0].msg, "only in the trust file of a project") || file.sizes != nil {
		t.Fatalf("a shipped file declares sizes: %+v", file.problems)
	}
	for text, want := range map[string]string{
		"256GB": "256000000000", "64GiB": "68719476736", "1 TB": "1000000000000", "7": "7", "12B": "12", "3KiB": "3072", "2MB": "2000000",
	} {
		got, err := parseMemory(text)
		if err != nil || got.String() != want {
			t.Errorf("parseMemory(%q) = %v, %v; want %s", text, got, err, want)
		}
	}
	for _, text := range []string{"", "GB", "-1GB", "1.5GB", "1e9", "0x10", "10 gigabytes"} {
		if got, err := parseMemory(text); err == nil {
			t.Errorf("parseMemory(%q) = %v, want an error", text, got)
		}
	}
}

// TestSizesReport checks what the trust report says of a declared memory:
// the claim with M and R, the reason, the count of obligations by package,
// and, on a platform where the bound on arrays is not below one
// allocation, that it proves nothing there (F6 of the design review).
func TestSizesReport(t *testing.T) {
	parallel(t)
	file := parseTrustFile("/work/vego-trusted.yaml", []byte("version: 1\nsizes:\n  memory: 256GB\n  reason: Our machines have 64 GB.\n"), false)
	if len(file.problems) > 0 {
		t.Fatal(file.problems)
	}
	uses := func(goarch string) []SizesUse {
		pv := &pkgVerifier{pass: &analysis.Pass{Pkg: types.NewPackage("example.com/"+goarch, goarch), TypesSizes: types.SizesFor("gc", goarch)},
			projectTrust: file, usage: &Usage{}}
		pv.noteSizes(file.path)
		return pv.usage.Sizes
	}
	wide := uses("amd64")
	wide[0].Proved = 3
	report := TrustReport([]*Usage{{Sizes: wide}, {Sizes: uses("386")}}, "/work")
	for _, want := range []string{
		"Memory declared in sizes: 1\n  vego-trusted.yaml:2\n",
		"claims:  the machines the program runs on never hold 256GB (256000000000 bytes) of its data at once, in memory and swap together, however it is stored",
		"every string, and the entries of every map, take at most 256000000000 bytes, and the array of every slice at most 1024000065536 bytes\n",
		"    leaves:  every size that a number gives, as the length of make, Grow, slices.Grow, and the count of Repeat, and every product of lengths, " +
			"as strings.Join and Replace over a slice, to be proved; a Variant may not rest on it\n",
		"    reason:  Our machines have 64 GB.\n",
		"    obligations only it proved: none in example.com/386: it proves nothing on this platform, where one allocation is at most 4294967295 bytes, " +
			"less than the 1024000065536 bytes it would bound an array by; 3 in example.com/amd64\n",
	} {
		if !strings.Contains(report, want) {
			t.Errorf("the report does not say %q:\n%s", want, report)
		}
	}
}

func TestUnreadableTrustFile(t *testing.T) {
	parallel(t)
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
	parallel(t)
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
	parallel(t)
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
	parallel(t)
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
