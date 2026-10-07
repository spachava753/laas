package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestLoadAPIKey(t *testing.T) {
	for _, test := range []struct {
		name, contents string
		valid          bool
	}{
		{"plain", "OPENAI_API_KEY=fake-key-not-secret\n", true},
		{"quoted", "export OPENAI_API_KEY='fake-key-not-secret'\nOTHER_KEY=ignore\n", true},
		{"missing", "OTHER_KEY=ignore\n", false},
		{"empty", "OPENAI_API_KEY=\n", false},
		{"duplicate", "OPENAI_API_KEY=\nOPENAI_API_KEY=fake-key-not-secret\n", false},
		{"whitespace", "OPENAI_API_KEY='fake-key-not-secret extra'\n", false},
	} {
		t.Run(test.name, func(t *testing.T) {
			t.Setenv("OPENAI_API_KEY", "")
			path := filepath.Join(t.TempDir(), "credential.env")
			if err := os.WriteFile(path, []byte(test.contents), 0o600); err != nil {
				t.Fatal(err)
			}
			err := loadAPIKey(path)
			if (err == nil) != test.valid {
				t.Fatalf("unexpected credential parsing result: %v", err)
			}
			if err != nil && strings.Contains(err.Error(), "fake-key-not-secret") {
				t.Fatal("credential appeared in diagnostic")
			}
			if test.valid && os.Getenv("OPENAI_API_KEY") != "fake-key-not-secret" {
				t.Fatal("wrong credential loaded")
			}
		})
	}
	t.Run("existing environment wins", func(t *testing.T) {
		t.Setenv("OPENAI_API_KEY", "fake-key-not-secret")
		if err := loadAPIKey(filepath.Join(t.TempDir(), "missing.env")); err != nil {
			t.Fatal("unexpected file read")
		}
	})
}
