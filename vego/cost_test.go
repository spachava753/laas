package vego

import (
	"bytes"
	"compress/gzip"
	"fmt"
	"io"
	"io/fs"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"
)

// TestCostFlag checks that -vego.cost prints what verifying each function
// asked of Z3, with the place of each question that stopped at the limit,
// that it changes no diagnostic, and that nothing is printed without it.
func TestCostFlag(t *testing.T) {
	alone(t)
	saved := costStderr
	defer func() { costStderr = saved }()
	kinds := map[string][len(questionNames)]int{}
	for _, flag := range []bool{false, true} {
		var out bytes.Buffer
		costStderr = &out
		analyzer := newAnalyzer()
		defer observe(analyzer, &observer{costs: func(pass *analysis.Pass, costs []*fnCost) {
			for _, c := range costs {
				kinds[c.fn.obj.FullName()] = c.kinds
			}
		}})()
		// What is printed is compared line by line, so answers come from
		// Z3 and not from a cache that VEGO_CACHE names.
		for name, value := range map[string]string{"cache": "", "rlimit": "600", "cost": map[bool]string{false: "false", true: "true"}[flag], "trusted": filepath.Join("testdata", "trusted.yaml")} {
			if err := analyzer.Flags.Set(name, value); err != nil {
				t.Fatal(err)
			}
		}
		// The diagnostics are those the corpus expects, with the flag
		// and without it.
		runCorpus(t, analyzer, "costs")
		if !flag {
			if out.Len() > 0 {
				t.Fatalf("without -vego.cost, printed %q", out.String())
			}
			continue
		}
		// Each question counts as what it is for: the kinds are, in
		// order, proof obligations, questions of the always-fails check,
		// contradiction checks, checks whether a Modifies entry is
		// needed, and quick checks.
		wantKinds := map[string][len(questionNames)]int{
			"costs.Add":     {3, 0, 1, 0, 0},
			"costs.Product": {7, 0, 1, 0, 0},
			"costs.Set":     {3, 0, 1, 2, 0},
			"costs.Read":    {0, 21, 3, 0, 2},
			"costs.read":    {0, 6, 2, 0, 0},
		}
		for fn, want := range wantKinds {
			if kinds[fn] != want {
				t.Errorf("%s asked %v questions of each kind, want %v", fn, kinds[fn], want)
			}
		}
		lines := strings.Split(strings.TrimRight(out.String(), "\n"), "\n")
		want := []string{
			`^/.*costs\.go:36:6: vego cost of the trusted contract of costs\.read: 8 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^\t/.*costs\.go:36:6: 4 questions of the always-fails check stopped at a limit$`,
			// The check of the entry and its first attempt both stop at
			// the limit of 600 units.
			`^\t/.*costs\.go:36:6: 2 contradiction checks stopped at a limit$`,
			`^/.*costs\.go:9:6: vego cost of Add: 4 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^/.*costs\.go:17:6: vego cost of Product: 8 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^\t/.*costs\.go:19:9: 2 proof obligations stopped at a limit$`,
			`^\t/.*costs\.go:20:11: 2 proof obligations stopped at a limit$`,
			`^/.*costs\.go:31:6: vego cost of Set: 6 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^/.*costs\.go:41:6: vego cost of Read: 26 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^\t/.*costs\.go:41:6: 8 questions of the always-fails check stopped at a limit$`,
			`^\t/.*costs\.go:42:2: 4 questions of the always-fails check stopped at a limit$`,
		}
		if len(lines) != len(want) {
			t.Fatalf("-vego.cost printed\n%s\nwant %d lines", out.String(), len(want))
		}
		for i, pattern := range want {
			if !regexp.MustCompile(pattern).MatchString(lines[i]) {
				t.Errorf("line %d is %q, want it to match %s", i+1, lines[i], pattern)
			}
		}
	}
}

// TestFailureTracking checks that a function that returns no error asks no
// question of the always-fails check, which nothing would read, while one
// that returns an error does; and that a trusted contract that never says
// it succeeds is still marked so in the trust report when only a function
// that returns no error calls it.
func TestFailureTracking(t *testing.T) {
	parallel(t)
	kinds := map[string][len(questionNames)]int{}
	analyzer := newAnalyzer()
	defer observe(analyzer, &observer{costs: func(pass *analysis.Pass, costs []*fnCost) {
		for _, c := range costs {
			kinds[c.fn.obj.FullName()] = c.kinds
		}
	}})()
	if err := analyzer.Flags.Set("trusted", filepath.Join("testdata", "trusted.yaml")); err != nil {
		t.Fatal(err)
	}
	graph := runCorpus(t, analyzer, "trackfail", "trackquiet")
	if n := kinds["trackfail.Passes"][failureCheck]; n == 0 {
		t.Errorf("Passes asked no question of the always-fails check")
	}
	for _, fn := range []string{"trackfail.Ignores", "trackquiet.Length"} {
		if n := kinds[fn][failureCheck]; n != 0 {
			t.Errorf("%s returns no error and asked %d questions of the always-fails check", fn, n)
		}
	}
	for _, action := range graph.Roots {
		usage := action.Result.(*Usage)
		found := false
		for _, use := range usage.Entries {
			if strings.HasSuffix(use.Key, ".parse") {
				found = true
				if !use.Unpredictable {
					t.Errorf("in %s, %s is not marked as failing unpredictably", action.Package.PkgPath, use.Key)
				}
			}
		}
		if !found {
			t.Errorf("in %s, the entry of parse is not in use", action.Package.PkgPath)
		}
	}
}

// TestAnswerCache runs corpus programs twice with -vego.cache, the second
// time with a solver of its own on the same directory: the second run
// answers every question from the directory, reports the same diagnostics
// and costs, says on standard error how many answers came from it, and
// names it in what the proofs rely on.
func TestAnswerCache(t *testing.T) {
	alone(t)
	root := t.TempDir()
	defer solver.SearchRepositoriesBelow(filepath.Dir(root))()
	saved := costStderr
	defer func() { costStderr = saved }()
	dir := filepath.Join(root, "cache")
	var printed [2]bytes.Buffer
	var costs [2]map[string]costLine
	var usages []*Usage
	// The two spellings of the directory are two solvers in the process,
	// so that the second reads what the first wrote instead of what its
	// process kept.
	for i, spelling := range []string{dir, dir + string(filepath.Separator)} {
		costStderr = &printed[i]
		analyzer := newAnalyzer()
		for name, value := range map[string]string{"cache": spelling, "trusted": filepath.Join("testdata", "trusted.yaml")} {
			if err := analyzer.Flags.Set(name, value); err != nil {
				t.Fatal(err)
			}
		}
		collected := collectCosts(analyzer)
		graph := runCorpus(t, analyzer, "defects", "paper")
		costs[i], _ = collected()
		if i == 1 {
			for _, action := range graph.Roots {
				usages = append(usages, action.Result.(*Usage))
			}
		}
	}
	if printed[0].Len() > 0 {
		t.Errorf("a run with nothing in the cache printed %q", printed[0].String())
	}
	if !maps.Equal(costs[0], costs[1]) || len(costs[0]) == 0 {
		t.Errorf("the costs differ with answers from the cache:\n%v\n%v", costs[0], costs[1])
	}
	for _, pkg := range []string{"defects", "paper"} {
		problems := 0
		for key, line := range costs[0] {
			if strings.HasPrefix(key, pkg+"\t") {
				problems += line.problems
			}
		}
		want := fmt.Sprintf("vego: %d of the %d answers of Z3 for %s came from the answer cache in %s\n", problems, problems, pkg, dir)
		if !strings.Contains(printed[1].String(), want) {
			t.Errorf("the second run printed %q, want a line %q", printed[1].String(), want)
		}
	}
	if report := TrustReport(usages, "."); !strings.Contains(report, "Answers of Z3 read from the answer cache: "+dir+"\n") {
		t.Errorf("the trust report does not name the cache:\n%s", report)
	}
}

// TestCacheErrorFailsTheRun checks that a cache error that the
// verification of one package meets fails every package verified after it
// in the run, whose own answers in the directory are sound: a run must not
// go on reading a directory it has shown wrong, whichever asker met the
// error. One entry of cachefaila is damaged, and cachefailb, which reads
// none of its entries, begins its functions only once the error is
// recorded. With speculation on and off, both packages fail with the same
// message.
func TestCacheErrorFailsTheRun(t *testing.T) {
	alone(t)
	root := t.TempDir()
	defer solver.SearchRepositoriesBelow(filepath.Dir(root))()
	dir := filepath.Join(root, "cache")
	found, err := exec.LookPath("z3")
	if err != nil {
		t.Fatal(err)
	}
	z3Dir, base := filepath.Split(found)
	// Each run has a solver of its own, by another spelling of the path of
	// Z3, since the error stays with the solver.
	run := func(dots int, speculate bool) map[string]string {
		t.Helper()
		analyzer := newAnalyzer()
		for name, value := range map[string]string{
			"z3": z3Dir + strings.Repeat("."+string(filepath.Separator), dots) + base, "cache": dir,
			"speculate": fmt.Sprint(speculate), "trusted": filepath.Join("testdata", "trusted.yaml"),
		} {
			if err := analyzer.Flags.Set(name, value); err != nil {
				t.Fatal(err)
			}
		}
		testdata, err := filepath.Abs("testdata")
		if err != nil {
			t.Fatal(err)
		}
		config := &packages.Config{
			Mode: packages.LoadAllSyntax,
			Dir:  filepath.Join(testdata, "src"),
			Env:  append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
		}
		defer heavy()()
		loaded, err := packages.Load(config, "cachefaila", "cachefailb")
		if err != nil || packages.PrintErrors(loaded) > 0 {
			t.Fatalf("load: %v", err)
		}
		graph, err := checker.Analyze([]*analysis.Analyzer{analyzer}, loaded, nil)
		if err != nil {
			t.Fatal(err)
		}
		failed := map[string]string{}
		for action := range graph.All() {
			if path := action.Package.PkgPath; path == "cachefaila" || path == "cachefailb" {
				failed[path] = fmt.Sprint(action.Err)
			}
		}
		return failed
	}
	if filled := run(5, false); filled["cachefaila"] != "<nil>" || filled["cachefailb"] != "<nil>" {
		t.Fatalf("the run that filled the cache failed: %v", filled)
	}
	// Damage the first entry, by name, of the problems that hold
	// cachefaila's number.
	var holding, others []string
	err = filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() {
			return err
		}
		// Only z3-<hash>/<2 hex>/<62 hex> is an entry.
		rel, err := filepath.Rel(dir, path)
		if parts := strings.Split(rel, string(filepath.Separator)); err != nil || len(parts) != 3 || !strings.HasPrefix(parts[0], "z3-") || strings.HasPrefix(parts[2], ".") {
			return err
		}
		content, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		if strings.Contains(entryProblem(t, content), "987654321") {
			holding = append(holding, path)
		} else {
			others = append(others, path)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(holding) == 0 || len(others) == 0 {
		t.Fatalf("%d entries hold the number of cachefaila and %d do not; want some of each", len(holding), len(others))
	}
	slices.Sort(holding)
	content, err := os.ReadFile(holding[0])
	if err != nil {
		t.Fatal(err)
	}
	content[len(content)-2] ^= 1
	if err := os.WriteFile(holding[0], content, 0o644); err != nil {
		t.Fatal(err)
	}
	verifying = func(pv *pkgVerifier, phase string) {
		if phase != "begin" || pv.pass.Pkg.Path() != "cachefailb" {
			return
		}
		s, err := solver.Open(pv.z3Path, pv.cacheDir)
		if err != nil {
			t.Error(err)
			return
		}
		for deadline := time.Now().Add(30 * time.Second); s.Untrusted() == nil; time.Sleep(10 * time.Millisecond) {
			if time.Now().After(deadline) {
				t.Error("no cache error was recorded within 30 seconds")
				return
			}
		}
	}
	defer func() { verifying = nil }()
	on, off := run(6, true), run(7, false)
	for _, failed := range []map[string]string{on, off} {
		for _, path := range []string{"cachefaila", "cachefailb"} {
			if !strings.Contains(failed[path], "is damaged") || !strings.Contains(failed[path], holding[0]) {
				t.Errorf("%s ended with %s, want the damaged entry %s", path, failed[path], holding[0])
			}
		}
	}
	if !maps.Equal(on, off) {
		t.Errorf("the packages end otherwise with speculation and without:\n%v\n%v", on, off)
	}
}

// entryProblem returns the text of the problem an entry of the answer cache
// is for; see encodeEntry in the solver.
func entryProblem(t *testing.T, content []byte) string {
	t.Helper()
	_, rest, _ := bytes.Cut(content, []byte("\n"))
	header, rest, _ := bytes.Cut(rest, []byte("\n"))
	var n int
	if _, err := fmt.Sscanf(string(header), "problem %d", &n); err != nil || n > len(rest) {
		t.Fatalf("an entry of the cache begins %q", header)
	}
	z, err := gzip.NewReader(bytes.NewReader(rest[:n]))
	if err != nil {
		t.Fatal(err)
	}
	text, err := io.ReadAll(z)
	if err != nil {
		t.Fatal(err)
	}
	return string(text)
}
