package main

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"context"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func TestGenerate(t *testing.T) {
	src := source{Repo: "example/repo", Commit: "abc", Split: "dev", License: "MIT"}
	original := []byte("package p\n// Sum adds two numbers.\nfunc Sum(a,b int) int { return a+b }\n")
	var archive bytes.Buffer
	zip := gzip.NewWriter(&archive)
	writer := tar.NewWriter(zip)
	for name, data := range map[string][]byte{"go.mod": []byte("module example/repo\n"), "LICENSE": []byte("MIT"), "p.go": original, "README.md": []byte("reference"), "../escape.go": []byte("bad"), ".github/hidden.go": []byte("hidden")} {
		if err := writer.WriteHeader(&tar.Header{Name: "repo-abc/" + name, Mode: 0o644, Size: int64(len(data)), Typeflag: tar.TypeReg}); err != nil {
			t.Fatal(err)
		}
		if _, err := writer.Write(data); err != nil {
			t.Fatal(err)
		}
	}
	if err := writer.Close(); err != nil {
		t.Fatal(err)
	}
	if err := zip.Close(); err != nil {
		t.Fatal(err)
	}
	src.ArchiveSHA256 = digest(archive.Bytes())
	root := t.TempDir()
	output := filepath.Join(root, "tasks")
	m := manifest{Version: "0.1.0", Sources: map[string]source{"repo": src}, Targets: []target{{ID: "sum", Source: "repo", File: "p.go", Symbol: "Sum", Kind: "function"}}}
	if err := writeJSON(filepath.Join(root, "manifest.json"), m); err != nil {
		t.Fatal(err)
	}
	if err := writeFile(filepath.Join(root, ".cache/abc.tar.gz"), archive.Bytes(), 0o644); err != nil {
		t.Fatal(err)
	}
	count, err := generate(context.Background(), root, output, "all")
	if err != nil || count != 1 {
		t.Fatalf("generate=%d err=%v", count, err)
	}
	t.Run("archive filtering", func(t *testing.T) {
		files, err := readArchive(archive.Bytes(), src)
		if err != nil {
			t.Fatal(err)
		}
		if !reflect.DeepEqual(sortedKeys(files), []string{"LICENSE", "go.mod", "p.go"}) {
			t.Fatalf("unsafe archive files: %v", sortedKeys(files))
		}
		src.ArchiveSHA256 = "incorrect"
		if _, err := fetchSource(context.Background(), root, src); err == nil {
			t.Fatal("unchecked archive")
		}
	})
	t.Run("Go verifier and isolation", func(t *testing.T) {
		var ref reference
		if err := readJSON(filepath.Join(output, "sum/tests/reference.json"), &ref); err != nil {
			t.Fatal(err)
		}
		stripped, err := os.ReadFile(filepath.Join(output, "sum/environment/repo/p.go"))
		if err != nil {
			t.Fatal(err)
		}
		if bytes.Contains(stripped, []byte("Sum adds")) {
			t.Fatal("answer leaked to agent")
		}
		inspection, err := inspect(stripped, "Sum")
		if err != nil || inspection.Fingerprint != ref.Fingerprint || inspection.Docs["$doc"].Text != "" {
			t.Fatal("stripping changed code")
		}
		dockerfile, err := os.ReadFile(filepath.Join(output, "sum/tests/Dockerfile"))
		if err != nil {
			t.Fatal(err)
		}
		if bytes.Contains(dockerfile, []byte("python")) || !bytes.Contains(dockerfile, []byte("CGO_ENABLED=0")) {
			t.Fatal("verifier is not native Go")
		}
		entries, err := os.ReadDir(filepath.Join(output, "sum/tests/tooling"))
		if err != nil {
			t.Fatal(err)
		}
		for _, entry := range entries {
			if strings.HasSuffix(entry.Name(), "_test.go") || strings.HasSuffix(entry.Name(), ".py") {
				t.Fatal("unexpected bundled tooling")
			}
		}
	})
	t.Run("refuses overwrite", func(t *testing.T) {
		before, err := os.ReadFile(filepath.Join(output, "sum/tests/reference.json"))
		if err != nil {
			t.Fatal(err)
		}
		if _, err := generate(context.Background(), root, output, "all"); err == nil {
			t.Fatal("overwrote existing dataset")
		}
		after, err := os.ReadFile(filepath.Join(output, "sum/tests/reference.json"))
		if err != nil || !bytes.Equal(before, after) {
			t.Fatal("existing task changed")
		}
	})
	t.Run("local validation", func(t *testing.T) {
		if err := validateTasks(context.Background(), output, filepath.Join(root, "reports"), &bytes.Buffer{}); err != nil {
			t.Fatal(err)
		}
		var results []validationResult
		if err := readJSON(filepath.Join(root, "reports/local-validation.json"), &results); err != nil {
			t.Fatal(err)
		}
		if len(results) != 1 || !results[0].RestoredReferenceGate || results[0].MissingDocsReward != 0 || results[0].Comments != 1 {
			t.Fatalf("invalid validation %v", results)
		}
	})
	t.Run("CLI config", func(t *testing.T) {
		config, err := os.ReadFile(filepath.Join(output, "sum/task.toml"))
		if err != nil {
			t.Fatal(err)
		}
		if !strings.Contains(string(config), `OPENAI_API_KEY = "${OPENAI_API_KEY}"`) {
			t.Fatal("credential template missing")
		}
		if err := commandMain(context.Background(), []string{"unknown"}, &bytes.Buffer{}); err == nil {
			t.Fatal("accepted unknown command")
		}
	})
}
