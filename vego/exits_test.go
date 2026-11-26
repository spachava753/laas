package vego

import (
	"errors"
	"fmt"
	"go/types"
	"log"
	"os"
	"os/exec"
	"strings"
	"testing"
)

// exitKeys are the shipped entries with exits. Each ends the process, so
// its harness runs it in a child process: this test binary, run again with
// -test.run=^TestChildCase$ and the case in VEGO_EXIT_CASE.
var exitKeys = []string{"os.Exit", "log.Fatal", "log.Fatalf", "log.Fatalln"}

// exitCase is what one run of a child process does, and what it must show.
type exitCase struct {
	name string
	// panicOnExit0 runs the child with -test.paniconexit0, as go test runs
	// a test binary.
	panicOnExit0 bool
	status       int
	// stderr is the text the child must write to standard error, or, with
	// panics, a text that standard error must contain.
	stderr   string
	panics   bool
	deferred bool // whether the call the child deferred ran
}

// exitCases holds, for each entry, the runs that show what it claims: that
// it ends the process, with which status, after writing what, without
// running deferred calls. os.Exit(0) under -test.paniconexit0 panics, and
// the deferred call runs, which is what the guide assumes away; log.Fatal
// exits with 1 either way.
var exitCases = map[string][]exitCase{
	"os.Exit": {
		{name: "exit3", status: 3},
		{name: "exit3", panicOnExit0: true, status: 3},
		{name: "exit0", status: 0},
		{name: "exit0", panicOnExit0: true, status: 2, panics: true, stderr: "unexpected call to os.Exit(0) during test", deferred: true},
	},
	"log.Fatal": {
		{name: "fatal", status: 1, stderr: fmt.Sprint("at", 1, "and", 2) + "\n"},
		{name: "fatal", panicOnExit0: true, status: 1, stderr: fmt.Sprint("at", 1, "and", 2) + "\n"},
	},
	"log.Fatalf": {
		{name: "fatalf", status: 1, stderr: fmt.Sprintf("%d-%s", 4, "x") + "\n"},
		{name: "fatalf", panicOnExit0: true, status: 1, stderr: fmt.Sprintf("%d-%s", 4, "x") + "\n"},
	},
	"log.Fatalln": {
		{name: "fatalln", status: 1, stderr: fmt.Sprintln("at", 1) + ""},
		{name: "fatalln", panicOnExit0: true, status: 1, stderr: fmt.Sprintln("at", 1)},
	},
}

// deferredMark is what a child writes to standard output when its deferred
// call runs.
const deferredMark = "the deferred call ran"

// TestChildCase is the body of a child process of checkExitEntry. Run
// without VEGO_EXIT_CASE, as every run of the tests does, it does nothing.
func TestChildCase(t *testing.T) {
	which := os.Getenv("VEGO_EXIT_CASE")
	if which == "" {
		return
	}
	defer fmt.Println(deferredMark)
	log.SetFlags(0)
	log.SetOutput(os.Stderr)
	switch which {
	case "exit3":
		os.Exit(3)
	case "exit0":
		os.Exit(0)
	case "fatal":
		log.Fatal("at", 1, "and", 2)
	case "fatalf":
		log.Fatalf("%d-%s", 4, "x")
	case "fatalln":
		log.Fatalln("at", 1)
	}
	t.Fatalf("unknown case %s", which)
}

// checkExitEntry checks the contract of a shipped entry with exits as vego
// reads it, and runs what the entry claims in child processes.
func checkExitEntry(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	fn := contractOfKey(t, pv, pkg, key)
	if !fn.exits || !neverReturns(fn) {
		t.Fatalf("%s is not read as a function that never returns: exits %v, ensures %d clauses", key, fn.exits, len(fn.ensures))
	}
	cases := exitCases[key]
	if len(cases) == 0 {
		t.Fatalf("no child process runs %s; add its cases to exitCases", key)
	}
	for _, c := range cases {
		args := []string{"-test.run=^TestChildCase$", "-test.count=1"}
		if c.panicOnExit0 {
			args = append(args, "-test.paniconexit0")
		}
		cmd := exec.Command(os.Args[0], args...)
		cmd.Env = append(os.Environ(), "VEGO_EXIT_CASE="+c.name)
		var stdout, stderr strings.Builder
		cmd.Stdout, cmd.Stderr = &stdout, &stderr
		err := cmd.Run()
		status := 0
		if exit := new(exec.ExitError); errors.As(err, &exit) {
			status = exit.ExitCode()
		} else if err != nil {
			t.Fatalf("%s (-test.paniconexit0 %v): %v", c.name, c.panicOnExit0, err)
		}
		what := fmt.Sprintf("%s with -test.paniconexit0 %v", c.name, c.panicOnExit0)
		if status != c.status {
			t.Errorf("%s exited with %d, not %d\nstdout: %s\nstderr: %s", what, status, c.status, stdout.String(), stderr.String())
		}
		if ran := strings.Contains(stdout.String(), deferredMark); ran != c.deferred {
			t.Errorf("%s: the deferred call ran: %v, not %v", what, ran, c.deferred)
		}
		switch {
		case c.panics && !strings.Contains(stderr.String(), c.stderr):
			t.Errorf("%s did not panic with %q: %s", what, c.stderr, stderr.String())
		case !c.panics && stderr.String() != c.stderr:
			t.Errorf("%s wrote %q to standard error, not %q", what, stderr.String(), c.stderr)
		}
	}
}
