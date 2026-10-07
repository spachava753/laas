package main

import (
	"crypto/sha256"
	"embed"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

//go:embed *.go
var tooling embed.FS

const (
	defaultRoot    = "evals/golang-docs"
	goImage        = "golang:1.27.1-bookworm"
	verifierImage  = "debian:bookworm-slim"
	harborVersion  = "0.24.0"
	maxSourceBytes = 4 << 20
)

type source struct {
	Repo          string `json:"repo"`
	Commit        string `json:"commit"`
	ArchiveSHA256 string `json:"archive_sha256"`
	Split         string `json:"split"`
	License       string `json:"license"`
}

type target struct {
	ID     string `json:"id"`
	Source string `json:"source"`
	File   string `json:"file"`
	Symbol string `json:"symbol"`
	Kind   string `json:"kind"`
}

type manifest struct {
	Version string            `json:"version"`
	Sources map[string]source `json:"sources"`
	Targets []target          `json:"targets"`
}

type reference struct {
	target
	Version     string              `json:"version"`
	Provenance  source              `json:"provenance"`
	SourceURL   string              `json:"source_url"`
	Docs        map[string]document `json:"docs"`
	Fingerprint string              `json:"fingerprint"`
	Declaration string              `json:"declaration"`
	Files       map[string]string   `json:"files"`
}

func digest(data []byte) string {
	hash := sha256.Sum256(data)
	return hex.EncodeToString(hash[:])
}

func writeFile(path string, data []byte, mode os.FileMode) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.WriteFile(path, data, mode)
}

func writeJSON(path string, value any) error {
	data, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		return err
	}
	return writeFile(path, append(data, '\n'), 0o644)
}

func readJSON(path string, value any) error {
	data, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	return json.Unmarshal(data, value)
}

func sortedKeys[V any](values map[string]V) []string {
	keys := make([]string, 0, len(values))
	for key := range values {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	return keys
}

// copyTree copies regular snapshot files without following symlinks.
func copyTree(from, to string) error {
	return filepath.WalkDir(from, func(path string, entry os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if entry.Type()&os.ModeSymlink != 0 {
			return fmt.Errorf("symlink in snapshot")
		}
		rel, err := filepath.Rel(from, path)
		if err != nil {
			return err
		}
		dest := filepath.Join(to, rel)
		if entry.IsDir() {
			return os.MkdirAll(dest, 0o755)
		}
		if !entry.Type().IsRegular() {
			return fmt.Errorf("non-regular snapshot file")
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		return writeFile(dest, data, 0o644)
	})
}

// writeTooling bundles only production Go sources with a standalone module.
// The verifier builds from these files without depending on the host checkout.
func writeTooling(dir string) error {
	entries, err := tooling.ReadDir(".")
	if err != nil {
		return err
	}
	for _, entry := range entries {
		if strings.HasSuffix(entry.Name(), "_test.go") {
			continue
		}
		data, err := tooling.ReadFile(entry.Name())
		if err != nil {
			return err
		}
		if err := writeFile(filepath.Join(dir, entry.Name()), data, 0o644); err != nil {
			return err
		}
	}
	return writeFile(filepath.Join(dir, "go.mod"), []byte("module laas-golang-docs-eval\n\ngo 1.26.6\n"), 0o644)
}
