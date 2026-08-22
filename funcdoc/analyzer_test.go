package funcdoc

import (
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	limitFlag := Analyzer.Flags.Lookup("limit")
	if limitFlag == nil {
		t.Fatal("Analyzer has no limit flag")
	}
	if limitFlag.DefValue != "10" {
		t.Fatalf("limit default = %s, want 10", limitFlag.DefValue)
	}

	includeTestsFlag := Analyzer.Flags.Lookup("include-tests")
	if includeTestsFlag == nil {
		t.Fatal("Analyzer has no include-tests flag")
	}
	if includeTestsFlag.DefValue != "false" {
		t.Fatalf("include-tests default = %s, want false", includeTestsFlag.DefValue)
	}

	analysistest.Run(t, analysistest.TestData(), Analyzer, "defaultlimit")
}

func TestAnalyzerConfiguredLimit(t *testing.T) {
	analyzer := newAnalyzer()
	if err := analyzer.Flags.Set("limit", "2"); err != nil {
		t.Fatalf("set limit: %v", err)
	}

	analysistest.Run(t, analysistest.TestData(), analyzer, "customlimit")
}

func TestAnalyzerIncludesTestFiles(t *testing.T) {
	analyzer := newAnalyzer()
	if err := analyzer.Flags.Set("limit", "2"); err != nil {
		t.Fatalf("set limit: %v", err)
	}
	if err := analyzer.Flags.Set("include-tests", "true"); err != nil {
		t.Fatalf("include tests: %v", err)
	}

	analysistest.Run(t, analysistest.TestData(), analyzer, "includetests")
}
