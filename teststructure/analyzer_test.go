package teststructure

import (
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	t.Run("reports flat tests", func(t *testing.T) {
		analysistest.Run(t, analysistest.TestData(), Analyzer, "structured")
	})
}
