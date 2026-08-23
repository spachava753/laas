package inlinehelper

import (
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	t.Run("uses the default statement limit", func(t *testing.T) {
		flag := Analyzer.Flags.Lookup("max-statements")
		if flag == nil {
			t.Fatal("Analyzer has no max-statements flag")
		}
		if flag.DefValue != "4" {
			t.Fatalf("max-statements default = %s, want 4", flag.DefValue)
		}

		analysistest.Run(t, analysistest.TestData(), Analyzer, "singleuse")
	})

	t.Run("supports a custom statement limit", func(t *testing.T) {
		analyzer := newAnalyzer()
		if err := analyzer.Flags.Set("max-statements", "1"); err != nil {
			t.Fatalf("set max statements: %v", err)
		}

		analysistest.Run(t, analysistest.TestData(), analyzer, "customlimit")
	})
}
