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
	saved := costStderr
	defer func() { costStderr = saved }()
	for _, flag := range []bool{false, true} {
		var out bytes.Buffer
		costStderr = &out
		analyzer := newAnalyzer()
		for name, value := range map[string]string{"rlimit": "600", "cost": map[bool]string{false: "false", true: "true"}[flag]} {
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
		var lines []string
		for _, line := range strings.Split(strings.TrimSpace(out.String()), "\n") {
			lines = append(lines, strings.ReplaceAll(line, filepath.Join("testdata", "src", "costs")+string(filepath.Separator), ""))
		}
		want := []string{
			`^/.*costs\.go:9:6: vego cost of Add: 4 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^/.*costs\.go:17:6: vego cost of Cube: 6 problems, \d+ resource units, \d+ bytes, \d+\.\d\d s$`,
			`^\t/.*costs\.go:19:11: 2 proof obligations stopped at a limit$`,
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
	saved := observeCosts
	defer func() { observeCosts = saved }()
	kinds := map[string][len(questionNames)]int{}
	observeCosts = func(pass *analysis.Pass, costs []*fnCost) {
		for _, c := range costs {
			kinds[c.fn.obj.FullName()] = c.kinds
		}
	}
	analyzer := newAnalyzer()
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
