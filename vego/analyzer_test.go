package vego

import (
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	t.Run("verifies annotated functions", func(t *testing.T) {
		analysistest.Run(t, analysistest.TestData(), Analyzer, "paper", "algorithms", "defects", "rejected", "leetcode", "semantics", "effects")
	})

	t.Run("audits specifications on request", func(t *testing.T) {
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("audit", "true"); err != nil {
			t.Fatalf("set audit: %v", err)
		}

		analysistest.Run(t, analysistest.TestData(), analyzer, "audit")
	})
}
