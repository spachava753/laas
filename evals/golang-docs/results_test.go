package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestSummarize(t *testing.T) {
	job := t.TempDir()
	for _, test := range []struct{ name, body string }{
		{"one", `{"task_name":"example","verifier_result":{"rewards":{"doc_quality":0.8}},"agent_result":{"n_input_tokens":10,"n_output_tokens":5,"n_cache_tokens":2,"cost_usd":0.1,"metadata":{"credential":"fake-secret"}}}`},
		{"two", `{"task_name":"example","verifier_result":{"rewards":{"doc_quality":1}}}`},
		{"failed", `{"task_name":"other","exception_info":{"exception_type":"InfrastructureFailure","exception_message":"fake-secret"}}`},
	} {
		if err := writeFile(filepath.Join(job, test.name, "result.json"), []byte(test.body), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if err := os.MkdirAll(filepath.Join(job, "unfinished"), 0o755); err != nil {
		t.Fatal(err)
	}
	result, err := summarizeJob(job)
	if err != nil {
		t.Fatal(err)
	}
	if result.Scored != 2 || result.Exceptions != 1 || len(result.Trials) != 3 || result.Statistics.Mean != 0.9 || result.Tasks["example"].Count != 2 {
		t.Fatalf("wrong aggregate %+v", result)
	}
	data, err := json.Marshal(result)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(data), "fake-secret") {
		t.Fatal("unsafe result fields retained")
	}
	for _, trial := range result.Trials {
		if trial.Trial == "one" && (trial.InputTokens != 10 || trial.CachedTokens != 2 || trial.OutputTokens != 5 || trial.CostUSD == nil || *trial.CostUSD != 0.1) {
			t.Fatal("usage fields lost")
		}
	}
	t.Run("empty job", func(t *testing.T) {
		if _, err := summarizeJob(t.TempDir()); err == nil {
			t.Fatal("unfinished job presented as completed")
		}
	})
}
