package vego

import (
	"fmt"
	"testing"
)

// TestJoinSummaries holds the join that ends the iteration of ownership
// summaries that do not settle: it keeps what either keeps, and a result
// is fresh only where both say so, unknown where either does, and from or
// inside what either names.
func TestJoinSummaries(t *testing.T) {
	parallel(t)
	a := &ownSummary{keeps: []bool{true, false}, results: []ownResultFact{{fresh: true, from: []int{0}}, {unknown: true}}}
	b := &ownSummary{keeps: []bool{false, false}, results: []ownResultFact{{fresh: false, from: []int{1}, inside: []int{0}}, {fresh: true}}}
	got := joinSummaries(a, b)
	want := &ownSummary{keeps: []bool{true, false}, results: []ownResultFact{{fresh: false, from: []int{0, 1}, inside: []int{0}}, {unknown: true}}}
	if fmt.Sprintf("%+v", got) != fmt.Sprintf("%+v", want) {
		t.Errorf("join = %+v, want %+v", got, want)
	}
	if again := joinSummaries(got, a); fmt.Sprintf("%+v", again) != fmt.Sprintf("%+v", got) {
		t.Errorf("a join is not settled by joining again: %+v", again)
	}
	if joinSummaries(nil, a) != nil || joinSummaries(a, nil) != nil {
		t.Error("a summary joined with none says something")
	}
}
