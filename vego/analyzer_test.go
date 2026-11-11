package vego

import (
	"bufio"
	"fmt"
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

		runCorpus(t, analyzer,
			"paper", "algorithms", "defects", "rejected", "leetcode", "semantics", "effects", "integers", "values", "trust",
			"lib", "client", "memory", "shapes", "invariants", "mapping", "badpred", "usesbadpred", "early", "settled")
	})

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
