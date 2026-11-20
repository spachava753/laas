package vego

import (
	"bufio"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"

	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/analysis"
)

// The cost of verifying each function of the corpus is recorded in
// testdata/costs.txt: the problems asked of Z3, the resources Z3 counted
// for them, and the problems it left open, at a limit or otherwise. A cached answer counts
// as Z3 counted it, so the numbers do not depend on which package asked
// first, and the questions come in a fixed order. With the Go version and
// architecture that recorded the table, every number must be the same: a
// function that costs more, or less, fails, so that a change that makes
// verification slower is seen where it happens and one that makes it
// faster records its gain. With another Go version the types of the
// standard library may change what is asked, and only growth of more than
// costSlack fails. A function that the table does not list, or that it
// lists and the corpus no longer verifies, fails too.

// costsFile is the table, and recordCosts the variable that rewrites it.
const (
	costsFile   = "costs.txt"
	recordCosts = "VEGO_RECORD_COSTS"
	costSlack   = 0.10
)

// costLine is what the table records of one function.
type costLine struct {
	problems, limits int
	effort           int64
}

// costEnv names the toolchain, the architecture, and Z3, which the exact
// numbers hold for.
func costEnv() string {
	return fmt.Sprintf("%s %s/%s z3 %s", runtime.Version(), runtime.GOOS, runtime.GOARCH, solver.Version)
}

// collectCosts sets observeCosts to gather the cost of every function, by
// its package and name, until the returned function is called, which
// returns them.
func collectCosts() func() map[string]costLine {
	saved := observeCosts
	var mu sync.Mutex
	costs := map[string]costLine{}
	observeCosts = func(pass *analysis.Pass, records []*fnCost) {
		mu.Lock()
		defer mu.Unlock()
		for _, c := range records {
			key := pass.Pkg.Path() + "\t" + c.fn.obj.FullName()
			line := costs[key]
			line.problems += c.problems
			line.effort += c.effort
			line.limits += c.open
			costs[key] = line
		}
	}
	return func() map[string]costLine {
		observeCosts = saved
		return costs
	}
}

// checkCosts compares the costs of the corpus with the table, or rewrites
// the table when recordCosts is set.
func checkCosts(t *testing.T, costs map[string]costLine) {
	t.Helper()
	path := filepath.Join("testdata", costsFile)
	if os.Getenv(recordCosts) != "" {
		var b strings.Builder
		fmt.Fprintf(&b, "# What verifying each function of the corpus asks of Z3: package, function, problems, resources counted, problems Z3 left open, at a limit or otherwise.\n")
		fmt.Fprintf(&b, "# Written by %s=1 go test ./vego -run 'TestAnalyzer/verifies'; see guard_test.go.\n", recordCosts)
		fmt.Fprintf(&b, "env %s\n", costEnv())
		for _, key := range slices.Sorted(func(yield func(string) bool) {
			for key := range costs {
				if !yield(key) {
					return
				}
			}
		}) {
			c := costs[key]
			fmt.Fprintf(&b, "%s\t%d\t%d\t%d\n", key, c.problems, c.effort, c.limits)
		}
		if err := os.WriteFile(path, []byte(b.String()), 0o644); err != nil {
			t.Fatal(err)
		}
		t.Logf("recorded the costs of %d functions in %s", len(costs), path)
		return
	}
	recorded, env, err := readCosts(path)
	if err != nil {
		t.Fatalf("%v; record the costs with %s=1", err, recordCosts)
	}
	exact := env == costEnv()
	if !exact {
		t.Logf("the costs were recorded with %s and this is %s, so only growth of more than %.0f%% fails", env, costEnv(), costSlack*100)
	}
	problems := compareCosts(recorded, costs, exact)
	slices.Sort(problems)
	for _, problem := range problems {
		t.Error(problem)
	}
	if len(problems) > 0 {
		t.Errorf("if the change in cost is meant, record it with %s=1 go test ./vego -run 'TestAnalyzer/verifies' and say in the commit why it changed", recordCosts)
	}
}

// compareCosts returns what is wrong with the costs measured against the
// recorded ones: exactly, or with slack for growth.
func compareCosts(recorded, costs map[string]costLine, exact bool) []string {
	var problems []string
	for key, c := range costs {
		was, ok := recorded[key]
		name := strings.ReplaceAll(key, "\t", " ")
		switch {
		case !ok:
			problems = append(problems, fmt.Sprintf("%s is not in the table: %d problems, %d resources counted, %d left open", name, c.problems, c.effort, c.limits))
		case exact && c != was:
			problems = append(problems, fmt.Sprintf("%s costs %d problems, %d resources counted, %d left open; the table has %d, %d, %d",
				name, c.problems, c.effort, c.limits, was.problems, was.effort, was.limits))
		case !exact && (grown(c.problems, was.problems) || grown(int(c.effort), int(was.effort)) || grown(c.limits, was.limits)):
			problems = append(problems, fmt.Sprintf("%s costs %d problems, %d resources counted, %d left open; the table has %d, %d, %d, and that is more than %.0f%% more",
				name, c.problems, c.effort, c.limits, was.problems, was.effort, was.limits, costSlack*100))
		}
	}
	for key := range recorded {
		if _, ok := costs[key]; !ok {
			problems = append(problems, fmt.Sprintf("%s is in the table and asked nothing", strings.ReplaceAll(key, "\t", " ")))
		}
	}
	return problems
}

// grown reports whether a number grew by more than the slack.
func grown(now, was int) bool {
	return float64(now) > float64(was)*(1+costSlack)
}

// readCosts reads the table and the environment it was recorded in.
func readCosts(path string) (map[string]costLine, string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, "", err
	}
	defer f.Close()
	costs := map[string]costLine{}
	env := ""
	lines := bufio.NewScanner(f)
	for number := 1; lines.Scan(); number++ {
		line := lines.Text()
		switch {
		case strings.HasPrefix(line, "#"):
			continue
		case strings.HasPrefix(line, "env "):
			env = strings.TrimPrefix(line, "env ")
			continue
		}
		fields := strings.Split(line, "\t")
		if len(fields) != 5 {
			return nil, "", fmt.Errorf("%s:%d: want 5 fields separated by tabs", path, number)
		}
		var c costLine
		var errs [3]error
		c.problems, errs[0] = strconv.Atoi(fields[2])
		c.effort, errs[1] = strconv.ParseInt(fields[3], 10, 64)
		c.limits, errs[2] = strconv.Atoi(fields[4])
		for _, err := range errs {
			if err != nil {
				return nil, "", fmt.Errorf("%s:%d: %v", path, number, err)
			}
		}
		costs[fields[0]+"\t"+fields[1]] = c
	}
	if env == "" {
		return nil, "", fmt.Errorf("%s does not say what it was recorded with", path)
	}
	return costs, env, lines.Err()
}

// TestCompareCosts checks the comparison of costs with the table.
func TestCompareCosts(t *testing.T) {
	recorded := map[string]costLine{"p\tf": {10, 1000, 1}, "p\tg": {5, 500, 0}}
	same := map[string]costLine{"p\tf": {10, 1000, 1}, "p\tg": {5, 500, 0}}
	tests := []struct {
		name  string
		costs map[string]costLine
		exact bool
		want  int
	}{
		{"the same", same, true, 0},
		{"one more problem", map[string]costLine{"p\tf": {11, 1000, 1}, "p\tg": {5, 500, 0}}, true, 1},
		{"fewer resources", map[string]costLine{"p\tf": {10, 999, 1}, "p\tg": {5, 500, 0}}, true, 1},
		{"one more left open", map[string]costLine{"p\tf": {10, 1000, 2}, "p\tg": {5, 500, 0}}, true, 1},
		{"a new function", map[string]costLine{"p\tf": {10, 1000, 1}, "p\tg": {5, 500, 0}, "p\th": {1, 1, 0}}, true, 1},
		{"a function gone", map[string]costLine{"p\tf": {10, 1000, 1}}, true, 1},
		{"growth within the slack", map[string]costLine{"p\tf": {11, 1100, 1}, "p\tg": {4, 400, 0}}, false, 0},
		{"growth past the slack", map[string]costLine{"p\tf": {10, 1101, 1}, "p\tg": {5, 500, 0}}, false, 1},
		{"a new function with slack", map[string]costLine{"p\tf": {10, 1000, 1}, "p\tg": {5, 500, 0}, "p\th": {1, 1, 0}}, false, 1},
	}
	for _, test := range tests {
		if got := compareCosts(recorded, test.costs, test.exact); len(got) != test.want {
			t.Errorf("%s: got %q, want %d problems", test.name, got, test.want)
		}
	}
}
