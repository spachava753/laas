package vego

import (
	"bufio"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"
)

var wantPattern = regexp.MustCompile("`([^`]*)`")

// runCorpus analyses packages under testdata/src and compares the
// diagnostics with the expectations in their sources. A line expects the
// diagnostics listed after "// want", each as a regular expression between
// backquotes; every diagnostic must be expected and every expectation met.
//
// This is the contract of analysistest.Run, which is not used here because
// it would also demand an expectation for every fact, and the analyzer
// exports one for each verified function.
func runCorpus(t *testing.T, analyzer *analysis.Analyzer, patterns ...string) {
	t.Helper()
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	config := &packages.Config{
		Mode: packages.LoadAllSyntax,
		Dir:  filepath.Join(testdata, "src"),
		Env:  append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	loaded, err := packages.Load(config, patterns...)
	if err != nil {
		t.Fatalf("load packages: %v", err)
	}
	if packages.PrintErrors(loaded) > 0 {
		t.Fatal("the test packages do not compile")
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{analyzer}, loaded, nil)
	if err != nil {
		t.Fatalf("analyze: %v", err)
	}
	type place struct {
		file string
		line int
	}
	wants := map[place][]*regexp.Regexp{}
	shown := func(file string) string {
		if rel, err := filepath.Rel(config.Dir, file); err == nil {
			return rel
		}
		return file
	}
	for _, action := range graph.Roots {
		if action.Err != nil {
			t.Fatalf("analysis of %s failed: %v", action.Package.PkgPath, action.Err)
		}
		for _, file := range action.Package.CompiledGoFiles {
			source, err := os.Open(file)
			if err != nil {
				t.Fatal(err)
			}
			lines := bufio.NewScanner(source)
			lines.Buffer(nil, 1<<20)
			for number := 1; lines.Scan(); number++ {
				_, expectations, found := strings.Cut(lines.Text(), "// want ")
				if !found {
					continue
				}
				for _, match := range wantPattern.FindAllStringSubmatch(expectations, -1) {
					wants[place{file, number}] = append(wants[place{file, number}], regexp.MustCompile(match[1]))
				}
			}
			source.Close()
		}
	}
	scanned := map[string]bool{}
	for _, action := range graph.Roots {
		for _, file := range action.Package.CompiledGoFiles {
			scanned[file] = true
		}
	}
	for _, action := range graph.Roots {
		for _, diagnostic := range action.Diagnostics {
			position := action.Package.Fset.Position(diagnostic.Pos)
			// A diagnostic may point into a trust file, which states its
			// expectations in the same way inside a YAML comment.
			if !scanned[position.Filename] {
				scanned[position.Filename] = true
				content, _ := os.ReadFile(position.Filename)
				for number, line := range strings.Split(string(content), "\n") {
					if _, expectations, found := strings.Cut(line, "// want "); found {
						for _, match := range wantPattern.FindAllStringSubmatch(expectations, -1) {
							at := place{position.Filename, number + 1}
							wants[at] = append(wants[at], regexp.MustCompile(match[1]))
						}
					}
				}
			}
			at := place{position.Filename, position.Line}
			index := slices.IndexFunc(wants[at], func(want *regexp.Regexp) bool { return want.MatchString(diagnostic.Message) })
			if index < 0 {
				t.Errorf("%s:%d:%d: unexpected diagnostic: %s", shown(position.Filename), position.Line, position.Column, diagnostic.Message)
				continue
			}
			wants[at] = slices.Delete(wants[at], index, index+1)
		}
	}
	var missing []string
	for at, remaining := range wants {
		for _, want := range remaining {
			missing = append(missing, fmt.Sprintf("%s:%d: no diagnostic was reported matching `%s`", shown(at.file), at.line, want))
		}
	}
	slices.Sort(missing)
	for _, message := range missing {
		t.Error(message)
	}
}

func TestAnalyzer(t *testing.T) {
	t.Run("verifies annotated functions", func(t *testing.T) {
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("trusted", filepath.Join("testdata", "trusted.yaml")); err != nil {
			t.Fatalf("set trusted: %v", err)
		}
		// The rejected corpus has tags of another tool, some declared here
		// and some not.
		if err := analyzer.Flags.Set("other-tags", "Summary, Param,x-order"); err != nil {
			t.Fatalf("set other-tags: %v", err)
		}

		runCorpus(t, analyzer,
			"paper", "algorithms", "defects", "rejected", "leetcode", "semantics", "effects", "ordering", "integers", "values", "trust",
			"lib", "client", "memory", "shapes", "badshapes", "invariants", "mapping", "badpred", "usesbadpred", "early", "settled", "gen", "earlytype", "earlyrange", "earlybox", "earlyloop", "earlycarrier", "earlypanic", "guide", "wrapped", "unread", "usesunread", "twovariants", "usestwovariants", "lonecr", "errorsid", "errorsvars", "errorsvarsclient", "vouched", "vouchedclient", "vouchedcapture", "earlyalias", "earlyaliasok", "sentinellib", "sentinelclient", "usesearly", "sentinelfar", "sentinelfarther", "closures", "funcvalues", "funcvalueslib", "funcvaluesclient", "funcvaluesunread", "funcvaluesinit", "funcvaluesinitdefer", "funcvaluesinitok", "funcvaluesinitmethod", "funcvaluesoldloop", "funcvaluesinitlit", "callbacks", "callbacksinit", "interfaces", "interfaceslib", "interfacesunread", "interfacesinitok", "interfacesinithand", "interfacesinitcall", "foreign", "stdtypes")
	})

	// The bound on the size of a formula stops a program whose formulas
	// grow faster than its text. That growth is what the program is for, so
	// the check that fails on it is off.
	t.Run("refuses a formula that grows beyond the limit", func(t *testing.T) {
		saved := growthRatio
		growthRatio = 0
		defer func() { growthRatio = saved }()
		runCorpus(t, newAnalyzer(), "toolarge")
	})

	// Each of these is the only package analysed, as when laas is run on
	// it alone: a dependency that changes an error variable is reported in
	// every package built with both it and a proof that relies on the
	// variable.
	for _, root := range []string{"gonelib", "gonemid", "goneroot", "gonereader", "wrapsp", "wrapsmid", "wrapsroot"} {
		t.Run("reports a changed error variable in "+root, func(t *testing.T) {
			runCorpus(t, newAnalyzer(), root)
		})
	}

	// Two modules give one type two entries. The packages that use them are
	// only dependencies here, as when laas is run on the main package, and
	// each alone is analysed without a report.
	t.Run("reports two entries for one type in a build", func(t *testing.T) {
		runCorpus(t, newAnalyzer(), "tworoot")
	})
	// A module whose proofs were made with no entry for a type, and one
	// that declares the type and has proofs that rest on it having none,
	// against a module that gives it an entry.
	t.Run("reports an entry against none in a build", func(t *testing.T) {
		runCorpus(t, newAnalyzer(), "twod")
	})
	// A module that gives (io.Closer).Close an entry of its own.
	t.Run("closes a body under a project entry", func(t *testing.T) {
		runCorpus(t, newAnalyzer(), "closer")
	})
	for _, root := range []string{"twoa", "twob", "twoc"} {
		t.Run("uses one entry for a type in "+root, func(t *testing.T) {
			runCorpus(t, newAnalyzer(), root)
		})
	}

	t.Run("refuses a trust file with a defect", func(t *testing.T) {
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("trusted", filepath.Join("testdata", "defective-trusted.yaml")); err != nil {
			t.Fatalf("set trusted: %v", err)
		}

		runCorpus(t, analyzer, "badtrust")
	})

	t.Run("refuses to verify for a caching driver", func(t *testing.T) {
		RefuseCachedRuns()
		defer func() { refuseCache = false }()

		runCorpus(t, newAnalyzer(), "refused")
	})

	t.Run("audits specifications on request", func(t *testing.T) {
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("audit", "true"); err != nil {
			t.Fatalf("set audit: %v", err)
		}

		runCorpus(t, analyzer, "audit")
	})
}

func TestOtherTagsFlag(t *testing.T) {
	tests := []struct {
		name, list string
		want       []string
		wantErr    string
	}{
		{name: "nothing declared", list: ""},
		{name: "several words with spaces around them", list: "Summary, Param ,x-order", want: []string{"Param", "Summary", "x-order"}},
		{name: "a keyword", list: "Summary,Ensures", wantErr: "too close"},
		{name: "a keyword but for a letter", list: "Ensure", wantErr: "too close"},
		{name: "a keyword but for its case", list: "requires", wantErr: "too close"},
		{name: "a retired keyword", list: "Measure", wantErr: "too close"},
		{name: "a retired keyword in another case", list: "measure", wantErr: "too close"},
		{name: "a planned keyword in another case", list: "cost", wantErr: "too close"},
		{name: "a keyword with its formula glued to it", list: "Ensures(1=2)", wantErr: "too close"},
		{name: "an assertion with its formula glued to it", list: "Assert(False)", wantErr: "too close"},
		{name: "a retired keyword with signs after it", list: "Measure(0)", wantErr: "too close"},
		{name: "a keyword behind signs", list: "(((Ensures", wantErr: "does not start with a letter"},
		{name: "an assertion behind signs", list: "###Assert", wantErr: "does not start with a letter"},
		{name: "an assertion behind digits", list: "123Assert", wantErr: "does not start with a letter"},
		{name: "a retired keyword behind a sign", list: "-Measure", wantErr: "does not start with a letter"},
		{name: "a keyword after other letters and a sign", list: "x-Ensures", wantErr: "too close"},
		{name: "two words in one", list: "Summary Param", wantErr: "not a single word"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got, err := parseOtherTags(test.list)
			switch {
			case test.wantErr != "" && (err == nil || !strings.Contains(err.Error(), test.wantErr)):
				t.Fatalf("got error %v, want one containing %q", err, test.wantErr)
			case test.wantErr == "" && err != nil:
				t.Fatalf("unexpected error: %v", err)
			}
			if tags := slices.Sorted(maps.Keys(got)); test.wantErr == "" && !slices.Equal(tags, test.want) {
				t.Fatalf("got %v, want %v", tags, test.want)
			}
		})
	}
}

// TestShownAnnotationsScan checks the pass that takes shown annotations out
// of a comment on inputs that would take minutes if it looked again from
// every slash of a long run of them.
func TestShownAnnotationsScan(t *testing.T) {
	slashes := strings.Repeat("/", 1<<20)
	tests := []struct {
		name, text, want string
	}{
		{name: "a run of slashes", text: " " + slashes, want: " " + slashes},
		{name: "a run of slashes in a string after a shown annotation", text: ` // @Ensures s = "` + slashes + `" and more`, want: "   s =   and more"},
		{name: "an empty string between two words after a shown annotation", text: ` // @Requires x @Ensures""Extra`, want: "   x @Ensures Extra"},
		{name: "a string inside a word after a shown annotation", text: ` // @Requires x @En"text"sures`, want: "   x @En sures"},
		{name: "a run of slashes in a string with nothing shown", text: ` see "` + slashes + `"`, want: ` see "` + slashes + `"`},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := withoutShown(test.text); got != test.want {
				t.Fatalf("got %d bytes starting %.40q, want %d bytes starting %.40q", len(got), got, len(test.want), test.want)
			}
		})
	}
}

// What the verifier builds must not grow faster than the program: a term
// that goes into a join of the ends of a function literal must not grow
// with the joins before it, and a value bound or stored must not be much
// larger as a tree than in memory. The tests catch either at once.
func init() {
	joinSizeLimit = 1 << 12
	growthRatio = 8
}
