package vego

import (
	"fmt"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// degenerate describes the final state of an implementation that ignores what
// the function is supposed to compute. It follows the adversarial archetypes
// of Anti-VeGo in the VeGo paper.
type degenerate struct {
	tag  string
	what string
	// result yields the value returned for result i; slice yields the final
	// contents of a slice parameter the function is allowed to write, which
	// must keep the parameter's own length, together with the facts that
	// define those contents.
	result func(i int, sort logic.Sort) *logic.Term
	slice  func(entry *logic.Term) (*logic.Term, []*logic.Term)
	facts  []*logic.Term
}

// audit probes the strength of a contract. Instead of checking the function's
// body, it asks whether implementations that do no real work would also
// satisfy the postcondition whenever the precondition holds. Each one that
// does exposes a property the specification forgot to demand.
func (v *fnVerifier) audit() {
	fn := v.fn
	if len(fn.ensures) == 0 {
		return
	}
	st := v.enter()
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	for _, candidate := range v.degenerates() {
		post := map[*types.Var]*logic.Term{}
		hyps := append(append([]*logic.Term(nil), st.hyps...), candidate.facts...)
		for _, param := range fn.params {
			post[param] = v.entry[param]
			if post[param].Sort.IsSeq() && v.mutates(fn, param) {
				var facts []*logic.Term
				post[param], facts = candidate.slice(v.entry[param])
				hyps = append(hyps, facts...)
			}
		}
		results := make([]*logic.Term, len(fn.results))
		for i, result := range fn.results {
			sort, _ := sortOf(result.Type())
			results[i] = candidate.result(i, sort)
		}
		env := &contractEnv{pv: v.pkgVerifier, fn: fn, args: v.entry, post: post, results: results}
		satisfied := true
		for _, c := range fn.ensures {
			satisfied = satisfied && solver.Prove(hyps, v.formula(c, c.node, env), opts) == solver.Proved
		}
		if satisfied {
			v.report(fn.decl.Name.Pos(), "specification of %s has a hole [%s]: it also accepts an implementation that %s",
				fn.obj.Name(), candidate.tag, candidate.what)
		}
	}
}

// degenerates lists the candidate implementations that make sense for the
// signature: constant results, results copied from a parameter, and slices
// overwritten with zeros or with the sequence 0, 1, 2, ...
func (v *fnVerifier) degenerates() []degenerate {
	fn := v.fn
	keep := func(entry *logic.Term) (*logic.Term, []*logic.Term) { return entry, nil }
	hasInt, hasBool, writesSlices := false, false, false
	var length *logic.Term = logic.IntLit(0)
	for _, result := range fn.results {
		sort, _ := sortOf(result.Type())
		hasInt = hasInt || sort == logic.Int
		hasBool = hasBool || sort == logic.Bool
		writesSlices = writesSlices || sort.IsSeq()
	}
	for i := len(fn.params) - 1; i >= 0; i-- {
		if entry := v.entry[fn.params[i]]; entry.Sort.IsSeq() {
			length = logic.Len(entry)
			writesSlices = writesSlices || v.mutates(fn, fn.params[i])
		}
	}
	constant := func(number int64, flag bool, fill func(sort logic.Sort) *logic.Term) func(int, logic.Sort) *logic.Term {
		return func(_ int, sort logic.Sort) *logic.Term {
			switch sort {
			case logic.Int:
				return logic.IntLit(number)
			case logic.Bool:
				return logic.BoolLit(flag)
			}
			return fill(sort)
		}
	}
	var list []degenerate
	for _, number := range []int64{0, 1, -1} {
		for _, flag := range []bool{false, true} {
			if (number != 0 && !hasInt) || (flag && !hasBool) {
				continue
			}
			tag, what := "CONSTANT", fmt.Sprintf("returns the constants %d and %t", number, flag)
			switch {
			case number == 0 && !flag:
				tag, what = "VACUOUS", "returns zero values"
			case !hasBool:
				what = fmt.Sprintf("returns the constant %d", number)
			case !hasInt:
				what = "returns true"
			}
			what += " and changes nothing"
			if len(fn.results) == 0 {
				what = "does nothing at all"
			}
			list = append(list, degenerate{tag: tag, what: what, result: constant(number, flag, zero), slice: keep})
		}
	}
	if writesSlices {
		zeros := func(length *logic.Term, sort logic.Sort) *logic.Term {
			return logic.Fill(length, zero(sort.Elem()))
		}
		list = append(list, degenerate{
			tag: "CONSTANT", what: "fills its slices with zero values",
			result: constant(0, false, func(sort logic.Sort) *logic.Term { return zeros(length, sort) }),
			slice: func(entry *logic.Term) (*logic.Term, []*logic.Term) {
				return zeros(logic.Len(entry), entry.Sort), nil
			},
		})
		// counting returns a sequence of the given length holding 0, 1, 2, ...
		counting := func(length *logic.Term, sort logic.Sort) (*logic.Term, []*logic.Term) {
			if sort != logic.IntSeq {
				return zeros(length, sort), nil
			}
			index := logic.Bound("k#audit", logic.Int)
			sequence := v.fresh("counting", logic.IntSeq)
			inRange := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, length))
			return sequence, []*logic.Term{
				logic.Eq(logic.Len(sequence), length),
				logic.Forall(index, logic.Implies(inRange, logic.Eq(logic.Select(sequence, index), index))),
			}
		}
		returned, facts := counting(length, logic.IntSeq)
		list = append(list, degenerate{
			tag: "OBLIVIOUS", what: "fills its slices with 0, 1, 2, ... whatever the input",
			result: constant(0, false, func(sort logic.Sort) *logic.Term {
				if sort == logic.IntSeq {
					return returned
				}
				return zeros(length, sort)
			}),
			slice: func(entry *logic.Term) (*logic.Term, []*logic.Term) {
				return counting(logic.Len(entry), entry.Sort)
			},
			facts: facts,
		})
	}
	for _, param := range fn.params {
		entry := v.entry[param]
		matches := false
		for _, result := range fn.results {
			sort, _ := sortOf(result.Type())
			matches = matches || sort == entry.Sort
		}
		if !matches {
			continue
		}
		list = append(list, degenerate{
			tag: "MINIMAL CONSTRUCTOR", what: "returns its argument " + param.Name() + " unchanged",
			result: func(_ int, sort logic.Sort) *logic.Term {
				if sort == entry.Sort {
					return entry
				}
				return zero(sort)
			},
			slice: keep,
		})
	}
	return list
}
