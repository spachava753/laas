package vego

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"
)

// TestTableChangedByTest checks that a package-level array a test of its
// package changes is not read as a table in the build with the tests, as
// laas builds a package by default (F7 of the design review of F36). The
// corpus runs builds without tests, where the array is a table.
func TestTableChangedByTest(t *testing.T) {
	parallel(t)
	defer heavy()()
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	config := &packages.Config{
		Mode:  packages.LoadAllSyntax,
		Tests: true,
		Dir:   filepath.Join(testdata, "src"),
		Env:   append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	loaded, err := packages.Load(config, "tables")
	if err != nil {
		t.Fatalf("load packages: %v", err)
	}
	if packages.PrintErrors(loaded) > 0 {
		t.Fatal("the test packages do not compile")
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{newAnalyzer()}, loaded, nil)
	if err != nil {
		t.Fatalf("analyze: %v", err)
	}
	const want = "cannot verify Tested: tested is assigned at tables_test.go:6; package-level arrays that are changed are not supported yet"
	withTests, without := false, false
	for _, action := range graph.Roots {
		found := false
		for _, diagnostic := range action.Diagnostics {
			found = found || strings.Contains(diagnostic.Message, want)
		}
		if strings.HasSuffix(action.Package.ID, ".test]") {
			withTests = withTests || found
		} else if !strings.HasSuffix(action.Package.PkgPath, ".test") {
			without = without || found
		}
	}
	if !withTests {
		t.Errorf("the build of tables with its tests did not report %q", want)
	}
	if without {
		t.Errorf("the build of tables without its tests reported %q, though it has no write", want)
	}
}
