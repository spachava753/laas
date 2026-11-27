package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

// TestSummary holds the counts of the summary to lines whose answers are
// known: what gets through, what a class stops alone, and the greedy
// order, by functions and with each module weighted equally.
func TestSummary(t *testing.T) {
	cause := func(class, detail string) event { return event{Class: class, Detail: detail, Kind: "cause"} }
	lines := []line{
		{Module: "a", Package: "a", Function: "Through"},
		{Module: "a", Package: "a", Function: "Assumed", Events: []event{{Class: "assumed:module", Kind: "assumed"}}},
		{Module: "a", Package: "a", Function: "Chan", Events: []event{cause("channel:use", ""), cause("channel:use", "")}},
		{Module: "a", Package: "a", Function: "ChanGo", Events: []event{cause("channel:use", ""), cause("goroutine:go", "")}},
		{Module: "a", Package: "a", Function: "Stat", Events: []event{cause("no-entry:std", "os.Stat")}},
		{Module: "a", Package: "a", Function: "Partial", Unseen: 2, Events: []event{cause("channel:use", "")}},
		{Module: "a", Package: "a", Function: "Proof", Events: []event{{Class: "append:call-in-target", Kind: "proof"}}},
		{Module: "b", Package: "b", Function: "Other", Events: []event{cause("no-entry:other", "x.F")}},
		{Module: "b", Package: "b", Function: "OtherChan", Events: []event{cause("no-entry:other", "x.F"), cause("channel:use", "")}},
		{Module: "b", Package: "b", Function: "Generated", Stopped: true, Events: []event{{Class: "skip:generated", Kind: "skip"}}},
	}
	dir := t.TempDir()
	path := filepath.Join(dir, "c.jsonl")
	var text []byte
	for _, l := range lines {
		b, err := json.Marshal(l)
		if err != nil {
			t.Fatal(err)
		}
		text = append(append(text, b...), '\n')
	}
	if err := os.WriteFile(path, text, 0o644); err != nil {
		t.Fatal(err)
	}
	var out bytes.Buffer
	if err := summary([]string{"-tsv", filepath.Join(dir, "c.tsv"), "c=" + path}, &out); err != nil {
		t.Fatal(err)
	}
	got := out.String()
	for _, want := range []string{
		// Through, Assumed, and Proof (past a proof class) get through.
		"- get through: 3 (33.3%), of which 1 only past refusals made when a proof fails",
		"- not looked at in full (a statement no attempt entered, or the census stopped): 1, with 2 statements not entered",
		// channel:use stops Chan, ChanGo, Partial, OtherChan; alone only Chan.
		"| `channel:use` | 4 | 1 | 3 | 1 |  |",
		"| `no-entry:std` | 1 | 1 | 1 | 0 | `os.Stat` (1, 1) |",
		// Greedy by classes: channel:use and no-entry:other first let one
		// through each, then no-entry:std; ties go by name.
		"| 1 | `channel:use` | 1 | 4 |",
		"| 2 | `no-entry:other` | 2 | 6 |",
		"| 3 | `goroutine:go` | 1 | 7 |",
		"| 4 | `no-entry:std` | 1 | 8 |",
		// Without no-entry:other, Other gets through from the start.
		"Get through with nothing fixed: 4.",
		// A function of a generated file is counted apart.
		"Functions of generated files, left out of every count above: 1.",
		// The proof classes are listed apart: Proof meets one and nothing
		// else.
		"| `append:call-in-target` | 1 | 1 |  |",
		// Each module weighted equally: a counts 7 functions of 1/7, b 2 of 1/2.
		"- functions with a body: 2.0, of which not loaded: 0.0",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("the summary has no line %q; it is:\n%s", want, got)
		}
	}
}

// TestNotLoaded holds notloaded to write a line for each function with a
// body that the census file has none for, as of a package that did not
// load, with an empty -skip leaving out nothing, and to leave out a file
// the build constraints of the host exclude (F25 of the review of F41).
func TestNotLoaded(t *testing.T) {
	dir := t.TempDir()
	files := map[string]string{
		"go.mod":         "module example.com/m\n\ngo 1.26\n",
		"a/a.go":         "package a\n\nfunc Loaded() {}\n",
		"b/b.go":         "package b\n\nfunc Broken() { undefined() }\n\ntype T struct{}\n\nfunc (t *T) M() {}\n",
		"b/b_windows.go": "package b\n\nfunc OnWindows() {}\n",
	}
	for name, text := range files {
		path := filepath.Join(dir, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	have := filepath.Join(dir, "census.jsonl")
	b, err := json.Marshal(line{Module: "example.com/m", Package: "example.com/m/a", Function: "Loaded"})
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(have, append(b, '\n'), 0o644); err != nil {
		t.Fatal(err)
	}
	var out bytes.Buffer
	if err := notLoaded([]string{"-module", "example.com/m", "-dir", dir, "-have", have, "-skip", ""}, &out); err != nil {
		t.Fatal(err)
	}
	var got []string
	for _, text := range strings.Split(strings.TrimSpace(out.String()), "\n") {
		var l line
		if err := json.Unmarshal([]byte(text), &l); err != nil {
			t.Fatal(err)
		}
		if len(l.Events) != 1 || l.Events[0].Class != "package:not-loaded" {
			t.Errorf("%s: events %+v", l.Function, l.Events)
		}
		got = append(got, l.Package+"."+l.Function)
	}
	slices.Sort(got)
	if want := []string{"example.com/m/b.(*T).M", "example.com/m/b.Broken"}; !slices.Equal(got, want) {
		t.Errorf("notloaded wrote %v, want %v", got, want)
	}
}
