package main

import (
	"encoding/json"
	"fmt"
	"io"
	"math"
	"os"
	"path/filepath"
)

type trialSummary struct {
	Task         string             `json:"task"`
	Trial        string             `json:"trial"`
	Score        *float64           `json:"score"`
	Members      map[string]float64 `json:"members,omitempty"`
	Exception    string             `json:"exception,omitempty"`
	InputTokens  int64              `json:"input_tokens"`
	OutputTokens int64              `json:"output_tokens"`
	CachedTokens int64              `json:"cached_tokens"`
	CostUSD      *float64           `json:"reported_cost_usd,omitempty"`
}
type scoreStats struct {
	Count             int     `json:"count"`
	Mean              float64 `json:"mean"`
	Minimum           float64 `json:"minimum"`
	Maximum           float64 `json:"maximum"`
	StandardDeviation float64 `json:"standard_deviation"`
}
type jobSummary struct {
	Job        string                `json:"job"`
	Scored     int                   `json:"scored"`
	Exceptions int                   `json:"exceptions"`
	Statistics scoreStats            `json:"statistics"`
	Tasks      map[string]scoreStats `json:"tasks"`
	Trials     []trialSummary        `json:"trials"`
}

// summarizeJob selects only scoring and usage fields from Harbor results.
// It intentionally excludes credentials, raw configuration, candidate comments,
// references, trajectories, and exception messages from tracked summaries.
func summarizeJob(dir string) (jobSummary, error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return jobSummary{}, err
	}
	summary := jobSummary{Job: filepath.Base(dir), Tasks: map[string]scoreStats{}, Trials: []trialSummary{}}
	values := []float64{}
	perTask := map[string][]float64{}
	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		path := filepath.Join(dir, entry.Name(), "result.json")
		var result struct {
			TaskName       string `json:"task_name"`
			TrialName      string `json:"trial_name"`
			VerifierResult *struct {
				Rewards map[string]float64 `json:"rewards"`
			} `json:"verifier_result"`
			ExceptionInfo *struct {
				Type string `json:"exception_type"`
			} `json:"exception_info"`
			AgentResult *struct {
				Input  int64    `json:"n_input_tokens"`
				Output int64    `json:"n_output_tokens"`
				Cached int64    `json:"n_cache_tokens"`
				Cost   *float64 `json:"cost_usd"`
			} `json:"agent_result"`
		}
		if err := readJSON(path, &result); os.IsNotExist(err) {
			continue
		} else if err != nil {
			return jobSummary{}, err
		}
		trial := trialSummary{Task: result.TaskName, Trial: entry.Name()}
		if result.AgentResult != nil {
			trial.InputTokens = result.AgentResult.Input
			trial.OutputTokens = result.AgentResult.Output
			trial.CachedTokens = result.AgentResult.Cached
			trial.CostUSD = result.AgentResult.Cost
		}
		if result.ExceptionInfo != nil {
			trial.Exception = result.ExceptionInfo.Type
			summary.Exceptions++
		}
		if result.VerifierResult != nil {
			if score, ok := result.VerifierResult.Rewards["doc_quality"]; ok {
				trial.Score = &score
				summary.Scored++
				values = append(values, score)
				perTask[trial.Task] = append(perTask[trial.Task], score)
				if err := readJSON(filepath.Join(dir, entry.Name(), "verifier/scores.json"), &trial.Members); err != nil && !os.IsNotExist(err) {
					return jobSummary{}, err
				}
			}
		}
		summary.Trials = append(summary.Trials, trial)
	}
	if len(summary.Trials) == 0 {
		return jobSummary{}, fmt.Errorf("no completed trial results in %s", dir)
	}
	summary.Statistics = statistics(values)
	for task, scores := range perTask {
		summary.Tasks[task] = statistics(scores)
	}
	return summary, nil
}

func statistics(values []float64) scoreStats {
	if len(values) == 0 {
		return scoreStats{}
	}
	stats := scoreStats{Count: len(values), Minimum: values[0], Maximum: values[0]}
	for _, value := range values {
		stats.Mean += value
		stats.Minimum = math.Min(stats.Minimum, value)
		stats.Maximum = math.Max(stats.Maximum, value)
	}
	stats.Mean /= float64(len(values))
	for _, value := range values {
		stats.StandardDeviation += (value - stats.Mean) * (value - stats.Mean)
	}
	stats.StandardDeviation = math.Sqrt(stats.StandardDeviation / float64(len(values)))
	return stats
}

// summarize prints sanitized aggregate results and optionally writes them as
// JSON. Infrastructure exceptions stay separate from scored candidate failures.
func summarize(jobs []string, output string, out io.Writer) error {
	results := []jobSummary{}
	for _, job := range jobs {
		result, err := summarizeJob(job)
		if err != nil {
			return err
		}
		results = append(results, result)
		fmt.Fprintf(out, "%s: scored=%d exceptions=%d mean=%.4f\n", result.Job, result.Scored, result.Exceptions, result.Statistics.Mean)
		for _, task := range sortedKeys(result.Tasks) {
			stats := result.Tasks[task]
			fmt.Fprintf(out, "  %s: n=%d mean=%.4f range=%.4f–%.4f\n", task, stats.Count, stats.Mean, stats.Minimum, stats.Maximum)
		}
	}
	if output != "" {
		return writeJSON(output, results)
	}
	return json.NewEncoder(out).Encode(results)
}
