package vego

import (
	"go/token"
	"go/types"
	"sync"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// The facts that a value fits in memory are bounds whose right side is a
// marked literal: the same number as the literal every other bound uses,
// so that a problem prints as it would without the mark, but a term of its
// own, so that the bound can be told from a bound on a number that a user
// or an entry wrote, by pointer. Only the places named at each mark make
// it.
type limitMarks struct {
	// mapCount bounds the number of keys of a map by MaxInt, and mapBytes
	// bounds what the entries of a map take by MaxAlloc (noteMap). Both
	// rest on memory alone: no obligation is asked where a key is added.
	mapCount, mapBytes *logic.Term
}

// marks returns the marked limits of the package's platform. They are made
// once for each platform and shared, so that a verifier copied for another
// platform, as the tests of 32-bit edges make, has the marks of its own.
func (pv *pkgVerifier) marks() *limitMarks {
	_, maxInt, _ := pv.intRange(types.Typ[types.Int])
	key := maxInt.String() + "/" + pv.maxAlloc().String()
	if found, ok := platformMarks.Load(key); ok {
		return found.(*limitMarks)
	}
	found, _ := platformMarks.LoadOrStore(key, &limitMarks{mapCount: logic.BigLit(maxInt), mapBytes: logic.BigLit(pv.maxAlloc())})
	return found.(*limitMarks)
}

// platformMarks holds the marks of each platform, by its MaxInt and
// MaxAlloc.
var platformMarks sync.Map

// memoryBacked returns the marks of the facts that are true only because a
// run cannot hold more than memory, with no obligation behind them where a
// value grows. A Variant may not rest on them: a loop that adds a key on
// every pass would otherwise be proved to end by the bound on the number of
// keys, and Go never returns from it (F1 of the design review of F38).
func (pv *pkgVerifier) memoryBacked() map[*logic.Term]bool {
	m := pv.marks()
	return map[*logic.Term]bool{m.mapCount: true, m.mapBytes: true}
}

// rewriteMarked rewrites each atom Le(t, mark) of a hypothesis, for a mark
// in marks, by with, where the atom stands only under And, Or, the
// consequent of Implies, and the body of a quantifier, the places where a
// weaker atom gives a weaker hypothesis and a stronger atom a stronger one.
// It reports false when a mark stands anywhere else, and the hypothesis is
// then to be left out (when weakening) or kept as it is (when
// strengthening).
func rewriteMarked(t *logic.Term, marks map[*logic.Term]bool, with func(*logic.Term) *logic.Term) (*logic.Term, bool) {
	if !holdsMark(t, marks) {
		return t, true
	}
	switch t.Op {
	case logic.OpLe:
		if marks[t.Args[1]] && !holdsMark(t.Args[0], marks) {
			return with(t), true
		}
		return t, false
	case logic.OpAnd, logic.OpOr:
		args := make([]*logic.Term, len(t.Args))
		for i, arg := range t.Args {
			rewritten, ok := rewriteMarked(arg, marks, with)
			if !ok {
				return t, false
			}
			args[i] = rewritten
		}
		if t.Op == logic.OpAnd {
			return logic.And(args...), true
		}
		return logic.Or(args...), true
	case logic.OpImplies:
		if holdsMark(t.Args[0], marks) {
			return t, false
		}
		rewritten, ok := rewriteMarked(t.Args[1], marks, with)
		if !ok {
			return t, false
		}
		return logic.Implies(t.Args[0], rewritten), true
	case logic.OpForall, logic.OpExists:
		if holdsMark(t.Args[0], marks) {
			return t, false
		}
		rewritten, ok := rewriteMarked(t.Args[1], marks, with)
		if !ok {
			return t, false
		}
		return logic.WithArgs(t, []*logic.Term{t.Args[0], rewritten}), true
	}
	return t, false
}

// holdsMark reports whether a term holds one of the marks.
func holdsMark(t *logic.Term, marks map[*logic.Term]bool) bool {
	if marks[t] {
		return true
	}
	for _, arg := range t.Args {
		if holdsMark(arg, marks) {
			return true
		}
	}
	return false
}

// withoutMarked returns the hypotheses with every marked bound dropped: an
// atom Le(t, mark) where it stands only to weaken becomes True, and a
// hypothesis that holds a mark anywhere else is left out. What follows from
// the result follows from the hypotheses.
func withoutMarked(hyps []*logic.Term, marks map[*logic.Term]bool) (out []*logic.Term, changed bool) {
	out = make([]*logic.Term, 0, len(hyps))
	for _, hyp := range hyps {
		rewritten, ok := rewriteMarked(hyp, marks, func(*logic.Term) *logic.Term { return logic.True() })
		changed = changed || !ok || rewritten != hyp
		if ok {
			out = append(out, rewritten)
		}
	}
	return out, changed
}

// checkVariant proves a goal of a Variant, bounded below or decreasing,
// without the facts that only memory makes true (memoryBacked). Proved so,
// it is assumed, as check assumes a goal. Not proved so but proved with
// them, the Variant holds only because a run cannot hold more than memory,
// and that is what the report says. Without a mark among the hypotheses the
// problem is the one check would ask.
func (v *fnVerifier) checkVariant(st *state, guard []*logic.Term, goal *logic.Term, pos token.Pos, format string, args ...any) {
	hyps, changed := withoutMarked(st.hyps, v.memoryBacked())
	done := v.at(pos)
	result := v.solver().Prove(append(hyps, guard...), goal, v.options(0, obligation))
	done()
	if result != solver.Proved && changed {
		done := v.at(pos)
		plain := v.attempt(st, guard, goal)
		done()
		if plain == solver.Proved {
			v.report(pos, format+"; it holds only because a map cannot have more keys than memory can hold, and a loop or a recursion that adds keys "+
				"until memory runs out does not end; the Variant must decrease for another reason, such as a count of what is left to do", args...)
			st.assume(logic.Implies(logic.And(guard...), goal))
			return
		}
	}
	v.answered(st, guard, goal, result, true, pos, format, args...)
}
