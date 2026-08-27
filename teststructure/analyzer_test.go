package teststructure

import (
	"slices"
	"testing"

	"golang.org/x/tools/go/analysis/analysistest"
)

func TestAnalyzer(t *testing.T) {
	t.Run("reports structural violations", func(t *testing.T) {
		analysistest.Run(t, analysistest.TestData(), Analyzer, "structured")
	})

	t.Run("follows Go test naming rules", func(t *testing.T) {
		tests := []struct {
			name string
			want bool
		}{
			{name: "Test", want: true},
			{name: "TestParser", want: true},
			{name: "Test_parser", want: true},
			{name: "Testhelper", want: false},
			{name: "testHelper", want: false},
		}
		for _, test := range tests {
			t.Run(test.name, func(t *testing.T) {
				if got := isTestName(test.name); got != test.want {
					t.Fatalf("isTestName(%q) = %t, want %t", test.name, got, test.want)
				}
			})
		}
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
