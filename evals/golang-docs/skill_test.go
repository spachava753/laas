package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestSkill(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "..", "skills", "golang-docs", "SKILL.md"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(data)
	lower := strings.ToLower(text)
	parts := strings.SplitN(text, "---\n", 3)
	if len(parts) != 3 || parts[0] != "" || !strings.Contains(parts[1], "name: golang-docs\n") || !strings.Contains(parts[1], "description: ") {
		t.Fatal("invalid skill frontmatter")
	}
	if len(strings.Fields(text)) > 1000 {
		t.Fatal("skill should remain a concise entrypoint")
	}
	var m manifest
	if err := readJSON("manifest.json", &m); err != nil {
		t.Fatal(err)
	}
	for _, src := range m.Sources {
		if strings.Contains(lower, strings.ToLower(src.Repo)) || strings.Contains(text, src.Commit) || strings.Contains(text, src.ArchiveSHA256) {
			t.Fatal("source provenance leaked into skill")
		}
	}
	for _, target := range m.Targets {
		for _, specific := range []string{target.ID, target.File, target.Symbol} {
			if strings.Contains(lower, strings.ToLower(specific)) {
				t.Fatalf("task identifier leaked into skill: %s", specific)
			}
		}
	}
	for _, specific := range []string{"/app/", "/tests/", "/solution/", "/home/", "/tmp/", ".go`", "gpt-6", "luna", "harbor", "decisions", "oracle", "doc_quality", "jsonschema", "go-sdk", "comment_0"} {
		if strings.Contains(lower, specific) {
			t.Fatalf("evaluation detail or literal path leaked: %s", specific)
		}
	}
	t.Run("development reference copying", func(t *testing.T) {
		for _, target := range m.Targets {
			if m.Sources[target.Source].Split != "dev" {
				continue
			}
			var ref reference
			if err := readJSON(filepath.Join("tasks", target.ID, "tests/reference.json"), &ref); os.IsNotExist(err) {
				continue
			} else if err != nil {
				t.Fatal(err)
			}
			for _, doc := range ref.Docs {
				if doc.Text != "" && strings.Contains(text, doc.Text) {
					t.Fatal("reference documentation copied into skill")
				}
			}
		}
	})
}
