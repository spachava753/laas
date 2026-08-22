package funcdoc

import (
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	flag := Analyzer.Flags.Lookup("limit")
	if flag == nil {
		t.Fatal("Analyzer has no limit flag")
	}
	if flag.DefValue != "10" {
		t.Fatalf("limit default = %s, want 10", flag.DefValue)
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
