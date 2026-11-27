package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
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
		// Each module weighted equally: a counts 7 functions of 1/7, b 2 of 1/2.
		"- functions with a body: 2.0, of which not loaded: 0.0",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("the summary has no line %q; it is:\n%s", want, got)
		}
	}
}
