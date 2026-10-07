package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestReflection(t *testing.T) {
	t.Run("redacts secret fields and strings", func(t *testing.T) {
		value := map[string]any{"api_key": "private-value", "items": []any{"sk-fake12345678", "OPENAI_API_KEY='private-value'", "Bearer private-value", "plain contract text"}}
		data, err := json.Marshal(sanitizeEvidence(value))
		if err != nil {
			t.Fatal(err)
		}
		if strings.Contains(string(data), "private-value") || strings.Contains(string(data), "sk-fake") {
			t.Fatal("credential was not redacted")
		}
		if !strings.Contains(string(data), "plain contract text") {
			t.Fatal("useful evidence lost")
		}
	})
	t.Run("packet scope and blinding", func(t *testing.T) {
		ref, repo, original, _ := newFixture(t)
		ref.Provenance.Split = "dev"
		root := t.TempDir()
		task := filepath.Join(root, "task")
		trial := filepath.Join(root, "trial")
		output := filepath.Join(root, "packet")
		if err := copyTree(repo, filepath.Join(task, "environment/repo")); err != nil {
			t.Fatal(err)
		}
		if err := writeJSON(filepath.Join(task, "tests/reference.json"), ref); err != nil {
			t.Fatal(err)
		}
		if err := writeFile(filepath.Join(task, "instruction.md"), []byte("Write docs."), 0o644); err != nil {
			t.Fatal(err)
		}
		candidate, err := inspect(original, ref.Symbol)
		if err != nil {
			t.Fatal(err)
		}
		request, _, err := makeRequest(ref, candidate)
		if err != nil {
			t.Fatal(err)
		}
		if err := writeJSON(filepath.Join(trial, "verifier/decision-request.json"), request); err != nil {
			t.Fatal(err)
		}
		if err := writeJSON(filepath.Join(trial, "result.json"), map[string]any{"score": 0.1, "secret": "private-value"}); err != nil {
			t.Fatal(err)
		}
		trajectory := `{"metadata":{"secret":"private-value"},"steps":[{"step_id":1,"source":"system","message":"secret system config"},{"step_id":2,"source":"agent","message":"Read evidence","reasoning_content":"private reasoning","tool_calls":[{"arguments":{"command":"echo OPENAI_API_KEY=private-value"}}]}]}`
		if err := writeFile(filepath.Join(trial, "agent/trajectory.json"), []byte(trajectory), 0o644); err != nil {
			t.Fatal(err)
		}
		if err := prepareReviewPacket(task, trial, output); err != nil {
			t.Fatal(err)
		}
		data, err := os.ReadFile(filepath.Join(output, "evidence.json"))
		if err != nil {
			t.Fatal(err)
		}
		for _, forbidden := range []string{"private-value", "private reasoning", "system config", "0.1", "gpt-6-luna"} {
			if strings.Contains(string(data), forbidden) {
				t.Fatalf("unblinded or sensitive field: %s", forbidden)
			}
		}
		if !strings.Contains(string(data), "Read evidence") {
			t.Fatal("trace evidence omitted")
		}
		if err := prepareReviewPacket(task, trial, output); err == nil {
			t.Fatal("overwrote packet")
		}
		ref.Provenance.Split = "holdout"
		if err := writeJSON(filepath.Join(task, "tests/reference.json"), ref); err != nil {
			t.Fatal(err)
		}
		if err := prepareReviewPacket(task, trial, filepath.Join(root, "holdout")); err == nil {
			t.Fatal("holdout entered tuning")
		}
	})
}
