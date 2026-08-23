package teststructure

import (
	"slices"
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	t.Run("reports shared test prefixes", func(t *testing.T) {
		analysistest.Run(t, analysistest.TestData(), Analyzer, "structured")
	})
}

func TestIdentifierWords(t *testing.T) {
	tests := []struct {
		name string
		want []string
	}{
		{name: "TestExampleSuccess", want: []string{"Example", "Success"}},
		{name: "TestHTTPClientFailure", want: []string{"HTTP", "Client", "Failure"}},
		{name: "TestParser_valid", want: []string{"Parser", "valid"}},
		{name: "TestVersion2Success", want: []string{"Version", "2", "Success"}},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := identifierWords(test.name); !slices.Equal(got, test.want) {
				t.Fatalf("identifierWords(%q) = %q, want %q", test.name, got, test.want)
			}
		})
	}
}
