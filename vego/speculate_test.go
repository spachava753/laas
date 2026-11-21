package vego

import (
	"errors"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"

	"github.com/spachava753/laas/vego/internal/solver"
)

// TestSpeculation checks that speculation changes nothing but time: corpus
// programs give the expected diagnostics and the same costs with it on and
// off, speculative verifiers did verify functions, and a speculative
// verifier that panics on every function changes nothing either. Each run
// has a solver of its own, by another spelling of the path of Z3, so that
// no run reads what another put into the solver's cache.
func TestSpeculation(t *testing.T) {
	alone(t)
	found, err := exec.LookPath("z3")
	if err != nil {
		t.Fatal(err)
	}
	dir, base := filepath.Split(found)
	spellings := []string{found, dir + "." + string(filepath.Separator) + base, dir + "." + string(filepath.Separator) + "." + string(filepath.Separator) + base}
	run := func(spelling string, speculate bool) map[string]costLine {
		analyzer := newAnalyzer()
		for name, value := range map[string]string{
			"z3": spelling, "speculate": map[bool]string{false: "false", true: "true"}[speculate],
			"trusted": filepath.Join("testdata", "trusted.yaml"), "cache": "",
		} {
			if err := analyzer.Flags.Set(name, value); err != nil {
				t.Fatal(err)
			}
		}
		collected := collectCosts(analyzer)
		runCorpus(t, analyzer, "algorithms", "deletes")
		costs, _ := collected()
		return costs
	}
	before := speculatedFunctions.Load()
	with := run(spellings[0], true)
	if speculatedFunctions.Load() == before {
		t.Error("no function was verified speculatively")
	}
	without := run(spellings[1], false)
	if !maps.Equal(with, without) || len(with) == 0 {
		t.Errorf("the costs differ with speculation and without:\n%v\n%v", with, without)
	}
	// A speculative verifier that panics is dropped, and the verification
	// verifies the function as always.
	panics := speculationPanics.Load()
	speculativeFault = func(fn *funcInfo) { panic("a fault of a speculative verifier") }
	defer func() { speculativeFault = nil }()
	faulty := run(spellings[2], true)
	if speculationPanics.Load() == panics {
		t.Error("no speculative verifier panicked")
	}
	if !maps.Equal(faulty, without) {
		t.Errorf("the costs differ when speculative verifiers panic:\n%v\n%v", faulty, without)
	}
}

// TestSpeculativeDistrust checks that an error that says the answer cache
// cannot be trusted, met by a speculative verifier after the verification
// of its package has asked its last question, fails that package: the
// verification waits for its speculative verifiers to stop before it ends.
// The order is forced: the verification begins once a speculative verifier
// has taken a function, and that verifier fails once the verification has
// verified every function. The run has a solver of its own, by another
// spelling of the path of Z3, since the error stays with the solver.
func TestSpeculativeDistrust(t *testing.T) {
	alone(t)
	found, err := exec.LookPath("z3")
	if err != nil {
		t.Fatal(err)
	}
	dir, base := filepath.Split(found)
	spelling := dir + strings.Repeat("."+string(filepath.Separator), 4) + base
	taken, finished := make(chan struct{}), make(chan struct{})
	var once sync.Once
	speculativeFault = func(fn *funcInfo) {
		first := false
		once.Do(func() { first = true })
		if !first {
			return
		}
		close(taken)
		select {
		case <-finished:
		case <-time.After(time.Minute):
			t.Error("the verification did not end its functions within a minute")
		}
		panic(&solver.CacheError{Err: errors.New("an entry found wrong by a speculative verifier")})
	}
	verifying = func(phase string) {
		switch phase {
		case "begin":
			select {
			case <-taken:
			case <-time.After(time.Minute):
				t.Error("no speculative verifier took a function within a minute")
			}
		case "end":
			close(finished)
		}
	}
	defer func() { speculativeFault, verifying = nil, nil }()
	analyzer := newAnalyzer()
	for name, value := range map[string]string{"z3": spelling, "trusted": filepath.Join("testdata", "trusted.yaml"), "cache": ""} {
		if err := analyzer.Flags.Set(name, value); err != nil {
			t.Fatal(err)
		}
	}
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	config := &packages.Config{
		Mode: packages.LoadAllSyntax,
		Dir:  filepath.Join(testdata, "src"),
		Env:  append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	defer heavy()()
	loaded, err := packages.Load(config, "algorithms")
	if err != nil || packages.PrintErrors(loaded) > 0 {
		t.Fatalf("load: %v", err)
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{analyzer}, loaded, nil)
	if err != nil {
		t.Fatal(err)
	}
	if got := graph.Roots[0].Err; got == nil || !strings.Contains(got.Error(), "found wrong by a speculative verifier") {
		t.Errorf("the package ended with %v, want the error the speculative verifier met", got)
	}
}
