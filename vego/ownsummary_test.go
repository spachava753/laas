package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
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

// TestWidenedSummaries holds the iteration of ownership summaries to end
// when the summary of a function goes round without settling: a summary
// whose error result is unknown every other time, as hcl's json parser's
// did, is widened to the join of the two, which says the result may be
// unknown and keeps what either keeps.
func TestWidenedSummaries(t *testing.T) {
	alone(t)
	calls := 0
	testSummarize = func(fn *funcInfo) *ownSummary {
		calls++
		if calls > 10000 {
			panic("the iteration of ownership summaries does not end")
		}
		odd := calls%2 == 1
		return &ownSummary{keeps: []bool{odd}, results: []ownResultFact{{fresh: true}, {unknown: odd}}}
	}
	defer func() { testSummarize = nil }()
	pkg := types.NewPackage("example.com/p", "p")
	sig := types.NewSignatureType(nil, nil, nil,
		types.NewTuple(types.NewParam(token.NoPos, pkg, "x", types.Typ[types.Int])),
		types.NewTuple(types.NewParam(token.NoPos, pkg, "n", types.Typ[types.Int]), types.NewParam(token.NoPos, pkg, "err", types.Universe.Lookup("error").Type())), false)
	fn := newFuncInfo(types.NewFunc(token.NoPos, pkg, "F", sig))
	fn.decl = &ast.FuncDecl{Name: ast.NewIdent("F"), Body: &ast.BlockStmt{}}
	fn.ensures = []*clause{{kind: "Ensures", text: "True"}}
	pv := &pkgVerifier{order: []*funcInfo{fn}, funcs: map[*types.Func]*funcInfo{fn.obj: fn}}
	got := pv.ownSummaryOf(fn)
	if got == nil || !got.keeps[0] || !got.results[1].unknown || !got.results[0].fresh {
		t.Errorf("the widened summary is %+v; it should keep x, with the error result unknown and the first fresh", got)
	}
}
