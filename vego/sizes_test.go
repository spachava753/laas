package vego

import (
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The declared memory is held back from every proof until step 2c of F38;
// the tests of the second try run with it.
func init() {
	sizesReady = true
}

// TestRewriteMarked checks where a marked bound is replaced: an atom
// Le(t, mark) under And, Or, the consequent of Implies, and a quantifier's
// body, where a smaller bound gives a stronger hypothesis and dropping it a
// weaker one; and nowhere else, where either would change what the
// hypothesis says in the other direction (F2 of the design review of F38).
func TestRewriteMarked(t *testing.T) {
	parallel(t)
	mark := logic.IntLit(1 << 48)
	marks := map[*logic.Term]bool{mark: true}
	x, y := logic.Const("x", logic.Int), logic.Const("y", logic.Int)
	smaller := logic.IntLit(1000)
	with := func(atom *logic.Term) *logic.Term { return logic.Le(atom.Args[0], smaller) }
	k := logic.Bound("k", logic.Int)
	positive := []*logic.Term{
		logic.Le(x, mark),
		logic.And(logic.Le(x, mark), logic.Le(y, logic.IntLit(3))),
		logic.Or(logic.Eq(x, logic.IntLit(0)), logic.Le(x, mark)),
		logic.Implies(logic.Le(y, logic.IntLit(3)), logic.Le(x, mark)),
		logic.Forall(k, logic.Implies(logic.Le(logic.IntLit(0), k), logic.Le(logic.Add(x, k), mark))),
	}
	for _, hyp := range positive {
		got, ok := rewriteMarked(hyp, marks, with)
		if !ok || holdsMark(got, marks) || !containsTerm(got, smaller) {
			t.Errorf("rewriteMarked(%s) = %s, %v; want the mark replaced", hyp, got, ok)
		}
	}
	elsewhere := []*logic.Term{
		logic.Not(logic.Le(x, mark)),
		logic.Implies(logic.Le(x, mark), logic.Le(y, logic.IntLit(3))),
		logic.Eq(x, mark),
		logic.Le(mark, x),
		logic.Le(logic.Add(x, mark), y),
		logic.Iff(logic.Le(x, mark), logic.Le(y, logic.IntLit(3))),
		logic.And(logic.Le(x, mark), logic.Not(logic.Le(y, mark))),
	}
	for _, hyp := range elsewhere {
		if got, ok := rewriteMarked(hyp, marks, with); ok {
			t.Errorf("rewriteMarked(%s) = %s; a mark that does not stand only as an upper bound in a weakening position must leave the hypothesis alone", hyp, got)
		}
	}
	unmarked := logic.Le(x, logic.IntLit(1<<48))
	if got, ok := rewriteMarked(unmarked, marks, with); !ok || got != unmarked {
		t.Errorf("rewriteMarked(%s) = %s, %v; a bound by the same number that is not the mark must stay", unmarked, got, ok)
	}
}

// containsTerm reports whether t holds sub, by pointer.
func containsTerm(t, sub *logic.Term) bool {
	if t == sub {
		return true
	}
	for _, arg := range t.Args {
		if containsTerm(arg, sub) {
			return true
		}
	}
	return false
}
