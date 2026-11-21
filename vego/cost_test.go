package vego

import (
	"bytes"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"golang.org/x/tools/go/analysis"
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
		for name, value := range map[string]string{"rlimit": "600", "cost": map[bool]string{false: "false", true: "true"}[flag], "trusted": filepath.Join("testdata", "trusted.yaml")} {
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
			"costs.read":    {0, 6, 1, 0, 0},
		}
		for fn, want := range wantKinds {
			if kinds[fn] != want {
				t.Errorf("%s asked %v questions of each kind, want %v", fn, kinds[fn], want)
			}
		}
		lines := strings.Split(strings.TrimRight(out.String(), "\n"), "\n")
		want := []string{
			`^/.*costs\.go:36:6: vego cost of the trusted contract of costs\.read: 7 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^\t/.*costs\.go:36:6: 4 questions of the always-fails check stopped at a limit$`,
			`^\t/.*costs\.go:36:6: 1 contradiction check stopped at a limit$`,
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
