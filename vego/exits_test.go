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
	// probed is set for a case that formats the operands of
	// TestPlainFormatting: what it writes is not checked, and no method of
	// a probe may run (F13 of the review of step 1 of F37).
	probed bool
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
		{name: "fatalprobe", status: 1, probed: true},
	},
	"log.Fatalf": {
		{name: "fatalf", status: 1, stderr: fmt.Sprintf("%d-%s", 4, "x") + "\n"},
		{name: "fatalf", panicOnExit0: true, status: 1, stderr: fmt.Sprintf("%d-%s", 4, "x") + "\n"},
		{name: "fatalfprobe", status: 1, probed: true},
	},
	"log.Fatalln": {
		{name: "fatalln", status: 1, stderr: fmt.Sprintln("at", 1)},
		{name: "fatalln", panicOnExit0: true, status: 1, stderr: fmt.Sprintln("at", 1)},
		{name: "fatallnprobe", status: 1, probed: true},
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
	probeMarks = true
	// Every verb and flag of probeFormat, over every operand.
	verbs := "%v %+v %#v %s %x %X %q %d %T %p %w %z %[1]v %[1]s %6.2v % x %-8q %[2]d %*d %.*s %! % %% text "
	switch which {
	case "fatalprobe":
		log.Fatal(plainOperands()...)
	case "fatalfprobe":
		log.Fatalf(strings.Repeat(verbs, 3), plainOperands()...)
	case "fatallnprobe":
		log.Fatalln(plainOperands()...)
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
		if strings.Contains(stdout.String(), probeMark) {
			t.Errorf("%s ran a method of a probe", what)
		}
		switch {
		case c.probed:
		case c.panics && !strings.Contains(stderr.String(), c.stderr):
			t.Errorf("%s did not panic with %q: %s", what, c.stderr, stderr.String())
		case !c.panics && stderr.String() != c.stderr:
			t.Errorf("%s wrote %q to standard error, not %q", what, stderr.String(), c.stderr)
		}
	}
}

// TestExitsInReport checks what the trust report says of an entry that
// never returns and of one that may end the process and returns otherwise
// (F15 of the review of step 1 of F37).
func TestExitsInReport(t *testing.T) {
	parallel(t)
	report := TrustReport([]*Usage{{
		ProjectKeys: map[string][]string{"/work/vego-trusted.yaml": {"example.com/app.Stop", "example.com/app.Must"}},
		Entries: []*EntryUse{
			{Key: "example.com/app.Stop", Reason: "Calls os.Exit.", File: "/work/vego-trusted.yaml", Line: 3, Exits: true, Never: true},
			{Key: "example.com/app.Must", Reason: "Calls os.Exit on a failure.", File: "/work/vego-trusted.yaml", Line: 9, Exits: true},
		},
	}}, "/work")
	never := "exits: a claim that the function ends the process as os.Exit does, without returning and without running deferred calls; nothing after a call of it is checked"
	may := "exits: a claim that the function may end the process as os.Exit does, without returning and without running deferred calls; nothing is checked on the path where it does, and where it returns its ensures hold"
	for key, want := range map[string]string{"example.com/app.Stop": never, "example.com/app.Must": may} {
		_, after, found := strings.Cut(report, key)
		if !found {
			t.Fatalf("the report does not name %s:\n%s", key, report)
		}
		if line, _, _ := strings.Cut(strings.SplitN(after, "\n", 3)[2], "\n"); strings.TrimSpace(line) != want {
			t.Errorf("the report says of %s %q, not %q", key, strings.TrimSpace(line), want)
		}
	}
}
