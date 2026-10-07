// Command golang-docs generates, validates, grades, and runs Harbor doc tasks.
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

func main() {
	ctx := context.Background()
	var err error
	if filepath.Base(os.Args[0]) == "docker" && os.Getenv(realDockerEnv) != "" {
		err = dockerShim(ctx, os.Args[1:])
	} else {
		err = commandMain(ctx, os.Args[1:], os.Stdout)
	}
	if err != nil {
		if exit, ok := err.(*exec.ExitError); ok {
			os.Exit(exit.ExitCode())
		}
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

// commandMain parses the repository CLI while forwarding run arguments intact
// to external Harbor. Grading and validation need no Harbor/Python dependency.
func commandMain(ctx context.Context, args []string, out io.Writer) error {
	if len(args) == 0 {
		return fmt.Errorf("usage: golang-docs {generate|validate|grade|inspect|run|summarize} [options]")
	}
	if args[0] == "run" {
		return runHarbor(ctx, defaultRoot, args[1:])
	}
	if args[0] == "inspect" {
		if len(args) != 2 {
			return fmt.Errorf("usage: golang-docs inspect SYMBOL < source.go")
		}
		data, err := io.ReadAll(io.LimitReader(os.Stdin, maxSourceBytes+1))
		if err != nil {
			return err
		}
		if len(data) > maxSourceBytes {
			return fmt.Errorf("source exceeds 4 MiB")
		}
		result, err := inspect(data, args[1])
		if err != nil {
			return err
		}
		return json.NewEncoder(out).Encode(result)
	}
	fs := flag.NewFlagSet(args[0], flag.ContinueOnError)
	fs.SetOutput(out)
	root := fs.String("root", defaultRoot, "eval tooling and manifest directory")
	switch args[0] {
	case "summarize":
		output := fs.String("output", "", "sanitized JSON report path")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		if fs.NArg() == 0 {
			return fmt.Errorf("summarize requires one or more job directories")
		}
		return summarize(fs.Args(), *output, out)
	case "generate":
		output := fs.String("output", "", "fresh task output directory (default ROOT/tasks)")
		split := fs.String("split", "all", "all, dev, or holdout")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		if *output == "" {
			*output = filepath.Join(*root, "tasks")
		}
		count, err := generate(ctx, *root, *output, *split)
		if err != nil {
			return err
		}
		fmt.Fprintf(out, "Generated %d Harbor tasks in %s\n", count, *output)
		return nil
	case "grade":
		refFile := fs.String("reference", "", "reference.json path")
		repo := fs.String("repo", "", "candidate module artifact")
		output := fs.String("output", "", "verifier log directory")
		requestOnly := fs.Bool("request-only", false, "save a validated request without calling OpenAI or writing a positive reward")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		if *refFile == "" || *repo == "" || *output == "" {
			return fmt.Errorf("grade requires --reference, --repo, and --output")
		}
		var ref reference
		if err := readJSON(*refFile, &ref); err != nil {
			return err
		}
		reward, err := grade(ctx, ref, *repo, *output, *requestOnly, liveClient())
		if err != nil {
			_ = writeJSON(filepath.Join(*output, "error.json"), map[string]string{"infrastructure_error": err.Error()})
			return err
		}
		if reward == nil {
			fmt.Fprintln(out, "Validated judge request (not graded)")
		} else {
			fmt.Fprintf(out, "doc_quality=%.4f\n", *reward)
		}
		return nil
	case "validate":
		tasks := fs.String("tasks", "", "generated dataset directory (default ROOT/tasks)")
		reports := fs.String("report-dir", "", "report directory (default ROOT/.cache/validation)")
		live := fs.Bool("live", false, "make six paid Decisions calibration requests; development tasks required")
		envFile := fs.String("env-file", "", "load only OPENAI_API_KEY for live calibration; never print it")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		if *tasks == "" {
			*tasks = filepath.Join(*root, "tasks")
		}
		if *reports == "" {
			*reports = filepath.Join(*root, ".cache/validation")
		}
		if err := validateTasks(ctx, *tasks, *reports, out); err != nil {
			return err
		}
		if *live {
			if *envFile != "" {
				if err := loadAPIKey(*envFile); err != nil {
					return err
				}
			}
			return calibrate(ctx, *tasks, *reports, out, liveClient())
		}
		return nil
	default:
		return fmt.Errorf("unknown command %q", args[0])
	}
}

func liveClient() decisionClient {
	return decisionClient{HTTP: &http.Client{Timeout: 60 * time.Second}, Endpoint: decisionsEndpoint, APIKey: os.Getenv("OPENAI_API_KEY"), RetryDelay: time.Second}
}

// loadAPIKey loads only the authorized judge credential. Existing process
// configuration takes precedence, and no secret values enter diagnostics.
func loadAPIKey(path string) error {
	if os.Getenv("OPENAI_API_KEY") != "" {
		return nil
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return fmt.Errorf("could not load credential file")
	}
	key := ""
	found := false
	for _, line := range strings.Split(string(data), "\n") {
		line = strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(line), "export "))
		name, value, ok := strings.Cut(line, "=")
		if !ok || strings.TrimSpace(name) != "OPENAI_API_KEY" {
			continue
		}
		if found {
			return fmt.Errorf("duplicate OPENAI_API_KEY assignments")
		}
		found = true
		key = strings.TrimSpace(value)
		if len(key) >= 2 && ((key[0] == '"' && key[len(key)-1] == '"') || (key[0] == '\'' && key[len(key)-1] == '\'')) {
			key = key[1 : len(key)-1]
		}
	}
	if key == "" || strings.ContainsAny(key, " \t\r\n") {
		return fmt.Errorf("credential file must contain one plain OPENAI_API_KEY assignment")
	}
	return os.Setenv("OPENAI_API_KEY", key)
}
