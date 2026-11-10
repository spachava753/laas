package vego

import (
	"fmt"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// degenerate describes an implementation that ignores what the function is
// supposed to compute. It follows the adversarial archetypes of Anti-VeGo in
// the VeGo paper.
type degenerate struct {
	tag  string
	what string
	// number and flag are the integers and booleans it returns.
	number int64
	flag   bool
	// fill gives the element at an index of every slice the function may
	// write and of every slice or string it returns; nil leaves the former
	// alone and returns empty ones.
	fill func(index *logic.Term, sort logic.Sort) *logic.Term
	// same, when set, is a parameter returned for every result of its type.
	same *types.Var
}

// filled returns an unknown sequence that holds the candidate's elements
// from lo up to hi, counted from lo, and the facts that say so.
func (v *fnVerifier) filled(candidate degenerate, sort logic.Sort, lo, hi *logic.Term) (*logic.Term, *logic.Term) {
	seq := v.fresh("filled", logic.SeqOf(sort))
	index := v.bound("k")
	inRange := logic.And(logic.Le(lo, index), logic.Lt(index, hi))
	element := logic.Eq(logic.Select(seq, index), candidate.fill(logic.Sub(index, lo), sort))
	return seq, logic.Forall(index, logic.Implies(inRange, element))
}

// audit probes the strength of a contract. Instead of checking the function's
// body, it asks whether implementations that do no real work would also
// satisfy the postcondition whenever the precondition holds. Each one that
// does exposes a property the specification forgot to demand.
//
// A candidate is only an implementation if everything it produces is a value
// of the right type: -1 is not a uint, an int argument is not an int8 unless
// the precondition makes it small enough, and a []byte cannot hold 0, 1, 2,
// ... beyond 255.
func (v *fnVerifier) audit() {
	fn := v.fn
	if len(fn.ensures) == 0 {
		return
	}
	entry := v.enter()
	for _, candidate := range v.degenerates() {
		st := entry.clone()
		wellTyped := true
		for _, t := range v.frame {
			sort, single := sortOf(t.typ)
			if !t.elems || !single || candidate.fill == nil {
				continue
			}
			lf := leaf{sort: sort, typ: t.typ}
			before := logic.Select(st.mem.region(t.owner(), logic.SeqOf(logic.SeqOf(sort))), t.ref)
			// A slice passed in is filled up to its length; what lies in
			// its capacity beyond that is left alone.
			hi := t.hi
			if t.param != nil {
				hi = logic.Add(t.lo, v.entry[t.param][2])
			}
			seq, content := v.filled(candidate, sort, t.lo, hi)
			index := v.bound("k")
			outside := logic.Or(logic.Lt(index, t.lo), logic.Le(hi, index))
			st.assume(content)
			st.assume(logic.Forall(index, logic.Implies(outside, v.same(logic.Select(seq, index), logic.Select(before, index)))))
			st.storeRow(t.owner(), lf, t.ref, seq)
			inRange := logic.And(logic.Le(t.lo, index), logic.Lt(index, hi))
			wellTyped = wellTyped && v.prove(st, nil, logic.Forall(index, logic.Implies(inRange, v.typeFact(logic.Select(seq, index), t.typ))))
		}
		results := make([]value, len(fn.results))
		for i, result := range fn.results {
			results[i] = v.degenerateResult(candidate, result.Type(), st)
			// An argument handed back is a value of its type already.
			if candidate.same == nil || !types.Identical(result.Type(), candidate.same.Type()) {
				// What a returned pointer refers to is not the candidate's
				// doing and is not asked about.
				typed := logic.And(v.wellFormed(results[i], result.Type(), st.brk), v.contentFacts(st.mem, results[i], result.Type(), st.brk, false))
				wellTyped = wellTyped && v.prove(st, nil, typed)
			}
		}
		if !wellTyped {
			continue
		}
		env := &specEnv{v: v, sink: st, fn: fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: entry.brk}
		satisfied := true
		for _, c := range fn.ensures {
			satisfied = satisfied && v.prove(st, nil, v.formula(c, c.node, env))
		}
		if satisfied {
			v.report(fn.decl.Name.Pos(), "specification of %s has a hole [%s]: it also accepts an implementation that %s",
				fn.obj.Name(), candidate.tag, candidate.what)
		}
	}
}

// degenerateResult builds what a candidate returns for a result of type t.
func (v *fnVerifier) degenerateResult(candidate degenerate, t types.Type, st *state) value {
	sort, single := sortOf(t)
	switch {
	case candidate.same != nil && types.Identical(t, candidate.same.Type()):
		return v.entry[candidate.same]
	case single && sort == logic.Int:
		return value{logic.IntLit(candidate.number)}
	case single && sort == logic.Bool:
		return value{logic.BoolLit(candidate.flag)}
	case candidate.fill == nil:
		return zeroValue(t)
	}
	length := v.lastLength()
	elem := types.Type(types.Typ[types.Uint8])
	if isSlice(t) {
		elem = elemType(t)
	}
	sort, single = sortOf(elem)
	if !single || (!isSlice(t) && !isString(t)) {
		return zeroValue(t)
	}
	seq, content := v.filled(candidate, sort, logic.IntLit(0), length)
	st.assume(content)
	if isString(t) {
		st.assume(logic.Eq(logic.Len(seq), length))
		return value{seq}
	}
	return v.allocSlice(st, elem, []*logic.Term{seq}, length, length)
}

// lastLength returns the length of the last slice parameter, which is the
// length a candidate gives the slices it returns, or zero without one.
func (v *fnVerifier) lastLength() *logic.Term {
	for i := len(v.fn.params) - 1; i >= 0; i-- {
		if entry := v.entry[v.fn.params[i]]; entry != nil && isSlice(v.fn.params[i].Type()) {
			return entry[2]
		}
	}
	return logic.IntLit(0)
}

// degenerates lists the candidate implementations that make sense for the
// signature: constant results, results copied from a parameter, and slices
// overwritten with zeros or with the sequence 0, 1, 2, ...
func (v *fnVerifier) degenerates() []degenerate {
	fn := v.fn
	hasInt, hasBool, writesSlices := false, false, false
	for _, result := range fn.results {
		sort, single := sortOf(result.Type())
		hasInt = hasInt || (single && sort == logic.Int)
		hasBool = hasBool || (single && sort == logic.Bool)
		writesSlices = writesSlices || isSlice(result.Type())
	}
	for _, t := range v.frame {
		writesSlices = writesSlices || t.elems
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
			list = append(list, degenerate{tag: tag, what: what, number: number, flag: flag})
		}
	}
	if writesSlices {
		zeros := func(_ *logic.Term, sort logic.Sort) *logic.Term { return zeroLeaf(leaf{sort: sort}) }
		list = append(list, degenerate{tag: "CONSTANT", what: "fills its slices with zero values", fill: zeros})
		list = append(list, degenerate{
			tag: "OBLIVIOUS", what: "fills its slices with 0, 1, 2, ... whatever the input",
			fill: func(index *logic.Term, sort logic.Sort) *logic.Term {
				if sort != logic.Int {
					return zeros(index, sort)
				}
				return index
			},
		})
	}
	for _, param := range fn.params {
		matches := false
		for _, result := range fn.results {
			matches = matches || types.Identical(result.Type(), param.Type())
		}
		if matches && v.entry[param] != nil {
			list = append(list, degenerate{
				tag: "MINIMAL CONSTRUCTOR", what: "returns its argument " + param.Name() + " unchanged", same: param,
			})
		}
	}
	return list
}
