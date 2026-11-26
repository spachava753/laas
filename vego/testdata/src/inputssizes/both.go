// Package inputssizes reads whole files under both declarations.
package inputssizes

import (
	"embed"
	"io"
	"os"
	"path/filepath"
	"strings"
)

// Config reads a file and upper-cases it, which the declared memory bounds.
//
// @Ensures True
func Config(path string) (text string, err error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	return strings.ToUpper(string(data)), nil
}

// All reads standard input and joins it to itself.
//
// @Ensures True
func All() (text string) {
	data, _ := io.ReadAll(os.Stdin)
	s := string(data)
	return s + s
}

// Summarize reads the result.json of every directory in a directory, as
// the trial's summarizeJob does.
//
// @Ensures n >= 0
func Summarize(dir string) (n int, err error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return 0, err
	}
	// @Invariant 0 <= n And n <= i
	for i := range entries {
		entry := entries[i]
		if !entry.IsDir() {
			continue
		}
		data, err := os.ReadFile(filepath.Join(dir, entry.Name(), "result.json"))
		if os.IsNotExist(err) {
			continue
		} else if err != nil {
			return 0, err
		}
		if len(data) > 0 {
			n++
		}
	}
	return n, nil
}

//go:embed files
var files embed.FS

// Copy writes every embedded file but those that end in .skip into a
// directory, as the trial's writeTooling does.
//
// @Ensures True
func Copy(dir string) (err error) {
	entries, err := files.ReadDir("files")
	if err != nil {
		return err
	}
	for _, entry := range entries {
		if strings.HasSuffix(entry.Name(), ".skip") {
			continue
		}
		data, err := files.ReadFile("files/" + entry.Name())
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(dir, entry.Name()), data, 0o644); err != nil {
			return err
		}
	}
	return nil
}
