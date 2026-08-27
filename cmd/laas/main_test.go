package main

import "testing"

func TestPackageFilter(t *testing.T) {
	var filter packageFilter
	if filter.Match("github.com/spachava753/laas/generated") {
		t.Fatal("empty filter matched a package")
	}

	if err := filter.Set(`(^|/)(generated|mocks)($|/)`); err != nil {
		t.Fatalf("set filter: %v", err)
	}
	if got, want := filter.String(), `(^|/)(generated|mocks)($|/)`; got != want {
		t.Fatalf("filter.String() = %q, want %q", got, want)
	}

	tests := []struct {
		path string
		want bool
	}{
		{path: "github.com/acme/project/generated", want: true},
		{path: "github.com/acme/project/mocks/http", want: true},
		{path: "github.com/acme/project/generator", want: false},
		{path: "github.com/acme/project/service", want: false},
	}
	for _, test := range tests {
		t.Run(test.path, func(t *testing.T) {
			if got := filter.Match(test.path); got != test.want {
				t.Fatalf("filter.Match(%q) = %t, want %t", test.path, got, test.want)
			}
		})
	}

	if err := filter.Set("["); err == nil {
		t.Fatal("invalid regular expression was accepted")
	}
	if !filter.Match("github.com/acme/project/generated") {
		t.Fatal("invalid update replaced the previous filter")
	}
}
