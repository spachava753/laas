package vego

import (
	"maps"
	"os/exec"
	"path/filepath"
	"testing"
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
