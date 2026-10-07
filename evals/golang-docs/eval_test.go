package main

import (
	"context"
	"encoding/json"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func newFixture(t *testing.T) (reference, string, []byte, []byte) {
	t.Helper()
	original := []byte("package p\n// Options configures work.\ntype Options struct {\n// Count is the maximum amount of work; zero means unlimited.\nCount int\n}\n// Other is unrelated.\nfunc Other() {}\n")
	parsed, err := inspect(original, "Options")
	if err != nil {
		t.Fatal(err)
	}
	stripped, err := stripComments(original, parsed.Ranges)
	if err != nil {
		t.Fatal(err)
	}
	repo := t.TempDir()
	if err := writeFile(filepath.Join(repo, "target.go"), original, 0o644); err != nil {
		t.Fatal(err)
	}
	ref := reference{target: target{ID: "fixture", File: "target.go", Symbol: "Options", Kind: "struct"}, Docs: parsed.Docs, Fingerprint: parsed.Fingerprint, Declaration: parsed.Declaration, Files: map[string]string{"target.go": digest(stripped)}}
	return ref, repo, original, stripped
}

func TestGrade(t *testing.T) {
	t.Run("structural gates", func(t *testing.T) {
		ref, repo, original, stripped := newFixture(t)
		cases := []struct {
			name string
			data []byte
			pass bool
		}{
			{"oracle", original, true},
			{"paraphrase", []byte(strings.ReplaceAll(string(original), "maximum amount of work", "work limit")), true},
			{"formatting", []byte(strings.ReplaceAll(string(original), "Count int", "Count    int")), true},
			{"stripped", stripped, false},
			{"missing field", []byte(strings.ReplaceAll(string(original), "// Count is the maximum amount of work; zero means unlimited.\n", "")), false},
			{"code changed", []byte(strings.ReplaceAll(string(original), "Count int", "Count string")), false},
			{"unrelated comment", []byte(strings.ReplaceAll(string(original), "Other is unrelated", "Other is different")), false},
			{"detached", []byte(strings.ReplaceAll(string(original), "// Options configures work.\n", "// Options configures work.\n\n")), false},
			{"unnamed", []byte(strings.ReplaceAll(string(original), "Options configures work", "Configure work here")), false},
			{"directive", []byte(strings.ReplaceAll(string(original), "// Options configures work.\n", "// Options configures work.\n//go:notinheap\n")), false},
		}
		for _, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				if err := os.WriteFile(filepath.Join(repo, "target.go"), test.data, 0o644); err != nil {
					t.Fatal(err)
				}
				_, failure, err := structuralGate(ref, repo)
				if err != nil || (failure == "") != test.pass {
					t.Fatalf("gate pass=%v failure=%q err=%v", failure == "", failure, err)
				}
			})
		}
	})
	t.Run("artifact changes", func(t *testing.T) {
		for _, kind := range []string{"extra", "missing", "symlink"} {
			t.Run(kind, func(t *testing.T) {
				ref, repo, _, _ := newFixture(t)
				switch kind {
				case "extra":
					if err := os.WriteFile(filepath.Join(repo, "extra.txt"), []byte("extra"), 0o644); err != nil {
						t.Fatal(err)
					}
				case "missing":
					if err := os.Remove(filepath.Join(repo, "target.go")); err != nil {
						t.Fatal(err)
					}
				case "symlink":
					if err := os.Remove(filepath.Join(repo, "target.go")); err != nil {
						t.Fatal(err)
					}
					if err := os.Symlink("outside.go", filepath.Join(repo, "target.go")); err != nil {
						t.Fatal(err)
					}
				}
				_, failure, err := structuralGate(ref, repo)
				if err != nil || failure == "" {
					t.Fatalf("unexpected gate: %q %v", failure, err)
				}
			})
		}
	})
	t.Run("request-only and failed regrade", func(t *testing.T) {
		ref, repo, _, _ := newFixture(t)
		logs := t.TempDir()
		if err := writeJSON(filepath.Join(logs, "reward.json"), map[string]int{"doc_quality": 1}); err != nil {
			t.Fatal(err)
		}
		value, err := grade(context.Background(), ref, repo, logs, true, decisionClient{})
		if err != nil || value != nil {
			t.Fatalf("request-only: %v %v", value, err)
		}
		if _, err := os.Stat(filepath.Join(logs, "reward.json")); !os.IsNotExist(err) {
			t.Fatal("stale reward exists")
		}
		if _, err := os.Stat(filepath.Join(logs, "decision-request.json")); err != nil {
			t.Fatal(err)
		}
		_, err = grade(context.Background(), ref, repo, logs, false, decisionClient{})
		if err == nil {
			t.Fatal("missing key did not fail")
		}
		if _, err := os.Stat(filepath.Join(logs, "reward.json")); !os.IsNotExist(err) {
			t.Fatal("failed regrade wrote reward")
		}
	})
	t.Run("nop never calls API", func(t *testing.T) {
		ref, repo, _, stripped := newFixture(t)
		if err := os.WriteFile(filepath.Join(repo, "target.go"), stripped, 0o644); err != nil {
			t.Fatal(err)
		}
		value, err := grade(context.Background(), ref, repo, t.TempDir(), false, decisionClient{})
		if err != nil || value == nil || *value != 0 {
			t.Fatalf("nop=%v err=%v", value, err)
		}
	})
}

func TestDecisions(t *testing.T) {
	ref, _, original, _ := newFixture(t)
	candidate, err := inspect(original, "Options")
	if err != nil {
		t.Fatal(err)
	}
	request, pairs, err := makeRequest(ref, candidate)
	if err != nil {
		t.Fatal(err)
	}
	t.Run("request schema", func(t *testing.T) {
		if request.Model != "gpt-6-luna" || len(request.Questions) != 2 || len(pairs) != 2 {
			t.Fatal("invalid request")
		}
		for _, q := range request.Questions {
			if q.Type != "score" || len(q.Levels) != 5 || !strings.Contains(q.Instructions, "untrusted DATA") {
				t.Fatal("invalid rubric")
			}
		}
		if pairs[0].Member != "$doc" || pairs[1].Member != "Count" || !strings.Contains(pairs[1].Reference, "zero means unlimited") {
			t.Fatal("field reference missing")
		}
		if strings.Contains(request.Input, "stripped_source_file") {
			t.Fatal("whole-file context reintroduced")
		}
	})
	t.Run("response validation", func(t *testing.T) {
		valid := `{"answers":[{"type":"score","name":"comment_1","score":2},{"type":"score","name":"comment_0","score":4}]}`
		scores, err := parseScores([]byte(valid), request)
		if err != nil || scores["comment_0"] != 1 || scores["comment_1"] != 0.5 {
			t.Fatalf("scores=%v err=%v", scores, err)
		}
		for _, data := range []string{`[]`, `{}`, `{"answers":[]}`, `{"answers":[{"type":"score","name":"comment_0","score":4}]}`, strings.ReplaceAll(valid, `"comment_1"`, `"comment_0"`), strings.ReplaceAll(valid, `"score":2`, `"score":true`), strings.ReplaceAll(valid, `"score":2`, `"score":"4"`), strings.ReplaceAll(valid, `"score":2`, `"score":null`), strings.ReplaceAll(valid, `"score":2`, `"score":5`), strings.ReplaceAll(valid, `"score":2`, `"score":-1`), strings.ReplaceAll(valid, `"score":2`, `"score":1e1000`)} {
			if _, err := parseScores([]byte(data), request); err == nil {
				t.Fatalf("accepted malformed response %s", data)
			}
		}
	})
	t.Run("HTTP and aggregation", func(t *testing.T) {
		calls := 0
		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			calls++
			if r.Method != "POST" || r.Header.Get("Authorization") != "Bearer fake-key" {
				t.Error("incorrect HTTP request")
			}
			var wire decisionRequest
			if err := json.NewDecoder(r.Body).Decode(&wire); err != nil {
				t.Error(err)
			}
			if wire.Model != decisionsModel || len(wire.Questions) != 2 {
				t.Error("invalid wire schema")
			}
			io.WriteString(w, `{"answers":[{"type":"score","name":"comment_0","score":4},{"type":"score","name":"comment_1","score":2}]}`)
		}))
		defer server.Close()
		ref, repo, _, _ := newFixture(t)
		value, err := grade(context.Background(), ref, repo, t.TempDir(), false, decisionClient{HTTP: server.Client(), Endpoint: server.URL, APIKey: "fake-key"})
		if err != nil || value == nil || *value != 0.75 || calls != 1 {
			t.Fatalf("grade=%v err=%v calls=%d", value, err, calls)
		}
	})
	t.Run("error and retry handling", func(t *testing.T) {
		for _, test := range []struct{ status, expected int }{{403, 1}, {429, 3}, {500, 3}} {
			t.Run(http.StatusText(test.status), func(t *testing.T) {
				calls := 0
				server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
					calls++
					w.WriteHeader(test.status)
					io.WriteString(w, "do not log fake-key")
				}))
				defer server.Close()
				_, err := (decisionClient{HTTP: server.Client(), Endpoint: server.URL, APIKey: "fake-key"}).call(context.Background(), request)
				if err == nil || calls != test.expected || strings.Contains(err.Error(), "fake-key") {
					t.Fatalf("unsafe error=%v calls=%d", err, calls)
				}
			})
		}
	})
}
