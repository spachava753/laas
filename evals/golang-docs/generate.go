package main

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"context"
	"fmt"
	"go/format"
	"io"
	"net/http"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"time"
)

// readArchive filters code, fixtures, and licenses from a pinned archive without
// extracting paths or following links; published docs and agent instructions
// are deliberately excluded from the agent snapshot.
func readArchive(data []byte, src source) (map[string][]byte, error) {
	reader, err := gzip.NewReader(bytes.NewReader(data))
	if err != nil {
		return nil, err
	}
	defer reader.Close()
	archive := tar.NewReader(reader)
	prefix := path.Base(src.Repo) + "-" + src.Commit + "/"
	files := map[string][]byte{}
	for {
		header, err := archive.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, err
		}
		if header.Typeflag != tar.TypeReg || !strings.HasPrefix(header.Name, prefix) {
			continue
		}
		name := strings.TrimPrefix(header.Name, prefix)
		if !safeArchivePath(name) {
			continue
		}
		if header.Size > maxSourceBytes {
			return nil, fmt.Errorf("archive file exceeds 4 MiB: %s", name)
		}
		contents, err := io.ReadAll(archive)
		if err != nil {
			return nil, err
		}
		files[name] = contents
	}
	if files["go.mod"] == nil || files["LICENSE"] == nil {
		return nil, fmt.Errorf("snapshot must contain go.mod and LICENSE")
	}
	return files, nil
}

// safeArchivePath excludes traversal, hidden files, and published documentation.
func safeArchivePath(name string) bool {
	if name == "" || path.IsAbs(name) || path.Clean(name) != name || strings.Contains(name, "\\") {
		return false
	}
	for _, part := range strings.Split(name, "/") {
		if part == ".." || part == "docs" || strings.HasPrefix(part, ".") {
			return false
		}
	}
	ext := strings.ToLower(path.Ext(name))
	return ext != ".md" && ext != ".rst"
}

// fetchSource checks cached or downloaded archive bytes against the manifest
// before decoding them; source URLs are public and require no credentials.
func fetchSource(ctx context.Context, root string, src source) (map[string][]byte, error) {
	cache := filepath.Join(root, ".cache", src.Commit+".tar.gz")
	data, err := os.ReadFile(cache)
	if os.IsNotExist(err) {
		request, err := http.NewRequestWithContext(ctx, http.MethodGet, "https://codeload.github.com/"+src.Repo+"/tar.gz/"+src.Commit, nil)
		if err != nil {
			return nil, err
		}
		client := &http.Client{Timeout: 60 * time.Second}
		response, err := client.Do(request)
		if err != nil {
			return nil, err
		}
		defer response.Body.Close()
		if response.StatusCode != http.StatusOK {
			return nil, fmt.Errorf("archive download returned HTTP %d", response.StatusCode)
		}
		data, err = io.ReadAll(io.LimitReader(response.Body, 64<<20+1))
		if err != nil {
			return nil, err
		}
		if len(data) > 64<<20 {
			return nil, fmt.Errorf("archive exceeds 64 MiB")
		}
	} else if err != nil {
		return nil, err
	}
	if digest(data) != src.ArchiveSHA256 {
		return nil, fmt.Errorf("archive checksum mismatch for %s", src.Repo)
	}
	if err := writeFile(cache, data, 0o644); err != nil {
		return nil, err
	}
	return readArchive(data, src)
}

func stripComments(data []byte, ranges []span) ([]byte, error) {
	masked := bytes.Clone(data)
	for _, r := range ranges {
		for i := r.Start; i < r.End; i++ {
			if masked[i] != '\n' && masked[i] != '\r' {
				masked[i] = ' '
			}
		}
	}
	return format.Source(masked)
}

// generate validates targets before writing, stages the complete dataset, and
// installs only new task directories. Existing tasks are never overwritten.
func generate(ctx context.Context, root, output, split string) (int, error) {
	var m manifest
	if err := readJSON(filepath.Join(root, "manifest.json"), &m); err != nil {
		return 0, err
	}
	if split != "all" && split != "dev" && split != "holdout" {
		return 0, fmt.Errorf("split must be all, dev, or holdout")
	}
	var targets []target
	seen := map[string]bool{}
	for _, t := range m.Targets {
		src, ok := m.Sources[t.Source]
		if !ok || !regexp.MustCompile(`^[a-z0-9]+(?:-[a-z0-9]+)*$`).MatchString(t.ID) || !safeArchivePath(t.File) || seen[t.ID] {
			return 0, fmt.Errorf("invalid or duplicate target %s", t.ID)
		}
		seen[t.ID] = true
		if split != "all" && src.Split != split {
			continue
		}
		if _, err := os.Lstat(filepath.Join(output, t.ID)); !os.IsNotExist(err) {
			return 0, fmt.Errorf("task %s exists or cannot be inspected; choose a fresh output directory", t.ID)
		}
		targets = append(targets, t)
	}
	if len(targets) == 0 {
		return 0, fmt.Errorf("no targets selected")
	}
	if err := os.MkdirAll(filepath.Dir(output), 0o755); err != nil {
		return 0, err
	}
	stage, err := os.MkdirTemp(filepath.Dir(output), ".golang-docs-generate-")
	if err != nil {
		return 0, err
	}
	defer os.RemoveAll(stage)
	archives := map[string]map[string][]byte{}
	for _, t := range targets {
		if archives[t.Source] == nil {
			files, err := fetchSource(ctx, root, m.Sources[t.Source])
			if err != nil {
				return 0, err
			}
			archives[t.Source] = files
		}
		if err := createTask(filepath.Join(stage, t.ID), filepath.Join(output, t.ID), t, m.Sources[t.Source], archives[t.Source], m.Version); err != nil {
			return 0, err
		}
	}
	if err := os.MkdirAll(output, 0o755); err != nil {
		return 0, err
	}
	for _, t := range targets {
		if err := os.Rename(filepath.Join(stage, t.ID), filepath.Join(output, t.ID)); err != nil {
			return 0, err
		}
	}
	return len(targets), nil
}

// createTask strips exactly the selected docs, verifies token identity and
// answer isolation, then writes the agent snapshot, oracle, and Go verifier.
func createTask(dir, display string, t target, src source, files map[string][]byte, version string) error {
	original, ok := files[t.File]
	if !ok {
		return fmt.Errorf("missing target file %s", t.File)
	}
	before, err := inspect(original, t.Symbol)
	if err != nil {
		return err
	}
	if before.Kind != t.Kind || before.Docs["$doc"].Text == "" {
		return fmt.Errorf("invalid documented target %s", t.ID)
	}
	for _, doc := range before.Docs {
		if t.Kind == "struct" && doc.Text == "" {
			return fmt.Errorf("struct %s has undocumented fields", t.ID)
		}
	}
	stripped, err := stripComments(original, before.Ranges)
	if err != nil {
		return err
	}
	after, err := inspect(stripped, t.Symbol)
	if err != nil {
		return err
	}
	if before.Fingerprint != after.Fingerprint {
		return fmt.Errorf("stripping changed code in %s", t.ID)
	}
	for _, doc := range after.Docs {
		if doc.Text != "" {
			return fmt.Errorf("target documentation remains in %s", t.ID)
		}
	}
	ref := reference{target: t, Version: version, Provenance: src, SourceURL: "https://github.com/" + src.Repo + "/blob/" + src.Commit + "/" + t.File, Docs: before.Docs, Fingerprint: before.Fingerprint, Declaration: after.Declaration, Files: map[string]string{}}
	rawDoc := original[before.Ranges[0].Start:before.Ranges[0].End]
	for name, data := range files {
		if name == t.File {
			data = stripped
		}
		if bytes.Contains(data, rawDoc) {
			return fmt.Errorf("reference comment duplicated in snapshot: %s", t.ID)
		}
		ref.Files[name] = digest(data)
		if err := writeFile(filepath.Join(dir, "environment/repo", filepath.FromSlash(name)), data, 0o644); err != nil {
			return err
		}
	}
	if err := writeJSON(filepath.Join(dir, "tests/reference.json"), ref); err != nil {
		return err
	}
	for _, folder := range []string{"tests", "solution"} {
		if err := writeFile(filepath.Join(dir, folder, "original.txt"), original, 0o644); err != nil {
			return err
		}
	}
	if err := writeTooling(filepath.Join(dir, "tests/tooling")); err != nil {
		return err
	}
	fields := ""
	if t.Kind == "struct" {
		fields = " and each of its fields"
	}
	outputs := map[string]string{
		"environment/Dockerfile": fmt.Sprintf("FROM %s\nWORKDIR /app/repo\nCOPY repo/ /app/repo/\nRUN go mod download\n", goImage),
		"tests/Dockerfile":       fmt.Sprintf("FROM %s AS build\nWORKDIR /src\nCOPY tooling/ /src/\nRUN CGO_ENABLED=0 go build -o /golang-docs-eval .\nFROM %s\nRUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/*\nCOPY --from=build /golang-docs-eval /usr/local/bin/golang-docs-eval\nCOPY . /tests/\nWORKDIR /app\n", goImage, verifierImage),
		"tests/test.sh":          "#!/bin/bash\nset -euo pipefail\nexec /usr/local/bin/golang-docs-eval grade --reference /tests/reference.json --repo /app/repo --output /logs/verifier\n",
		"solution/solve.sh":      "#!/bin/bash\nset -euo pipefail\ncp /solution/original.txt " + strconv.Quote("/app/repo/"+t.File) + "\n",
		"instruction.md":         fmt.Sprintf("Write an idiomatic Go doc comment for `%s`%s in\n`/app/repo/%s`. The comments have been removed.\n\nRead the implementation and surrounding package code to understand its contract.\nModify that file in place. Only change the requested comments; leave all code,\nother comments, and other files unchanged. Do not retrieve upstream documentation\nor use the network to look up the answer. Do not just describe the signature.\n", t.Symbol, fields, t.File),
		"task.toml":              fmt.Sprintf(taskTemplate, t.ID, version, t.Symbol, src.Split, t.Kind, src.Repo, src.Commit),
		"README.md":              fmt.Sprintf("# %s\n\nDocument `%s`%s; see [instruction.md](instruction.md).\nSource: [%s at `%s`](%s), %s license; split `%s`.\nOriginal licenses and copyright notices are retained.\n\nThe agent uses `%s` (1 CPU, 2 GiB, 300 seconds).\nThe separate verifier uses `%s`, a static Go grader, and CA certificates\n(1 CPU, 512 MiB, 300 seconds). No Python runs in the verifier.\n\n- `environment/`: stripped source, fixtures, license, agent Dockerfile.\n- `solution/`: original file and Oracle restoration script.\n- `tests/`: reference, Go sources, verifier Dockerfile and entrypoint.\n\nThe verifier rejects forbidden edits and missing docs, then scores each comment\nfrom 0 to 4 using `gpt-6-luna` through Decisions. The mean normalized score is\n`doc_quality`. Requests, responses, probabilities and per-comment scores are saved.\nAPI failures abort without a reward. Paraphrases are valid; Oracle scores are\nprobabilistic and need not equal 1.0.\n\nFrom the repository root:\n\n```sh\ngo run ./evals/golang-docs run -p %s -a oracle --env-file .env -y\ngo run ./evals/golang-docs run -p %s -a terminus-2 -m 'openai/<model>' --env-file .env -y\n```\n\nThe Go runner uses external Harbor %s and preserves hostname restrictions while\nallowing only Docker's configured upstream DNS servers on UDP/TCP port 53.\nSee the dataset README for calibration, isolation, and benchmark limitations.\n", t.ID, t.Symbol, fields, src.Repo, src.Commit, ref.SourceURL, src.License, src.Split, goImage, verifierImage, display, display, harborVersion),
	}
	for name, text := range outputs {
		mode := os.FileMode(0o644)
		if strings.HasSuffix(name, ".sh") {
			mode = 0o755
		}
		if err := writeFile(filepath.Join(dir, filepath.FromSlash(name)), []byte(text), mode); err != nil {
			return err
		}
	}
	return nil
}

const taskTemplate = `schema_version = "1.4"
artifacts = ["/app/repo"]

[task]
name = "laas/%s"
version = "%s"
description = "Document %s in Go"
keywords = ["go", "documentation", "judge-grading", "golang-docs"]

[metadata]
category = "programming"
difficulty = "medium"
split = "%s"
kind = "%s"
source_repo = "%s"
source_commit = "%s"

[agent]
timeout_sec = 300.0
network_mode = "allowlist"
allowed_hosts = ["api.openai.com", "api.anthropic.com"]

[environment]
network_mode = "public"
build_timeout_sec = 600.0
cpus = 1
memory_mb = 2048
storage_mb = 4096

[verifier]
timeout_sec = 300.0
environment_mode = "separate"

[verifier.env]
OPENAI_API_KEY = "${OPENAI_API_KEY}"

[verifier.environment]
network_mode = "allowlist"
allowed_hosts = ["api.openai.com"]
cpus = 1
memory_mb = 512
storage_mb = 1024
`
