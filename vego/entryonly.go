package vego

import (
	"fmt"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// An Ensures speaks of the state on return through the results, primed
// paths, and fresh. A conjunct of one that has none of these is a fact
// about the state when the function is called, which the Requires and the
// types alone must give, since no body changes that state. Where it reads
// memory the function may modify, its author most likely meant the value
// on return: an Ensures p.x = 7 on a function that sets p.x reads p.x on
// entry, and verifies whenever the Requires says so. Such a conjunct is
// refused. One that reads only what the function cannot change says the
// same of entry and return, and is kept.
//
// Whether a conjunct reads what the function may modify is decided by
// proof: its value in the state on entry, and in the same state after
// everything the Modifies clauses list was forgotten, must be proved
// equal. A read that may lie in a listed target, whatever path reaches it,
// a predicate's or a quantifier's included, makes the proof fail.

// entryOnly returns, for each conjunct of an Ensures of the function that
// speaks only of the entry state and reads memory the function may modify,
// the clause and a path of it written as the value on return. st is the
// state on entry.
func (v *fnVerifier) entryOnly(st *state) []entryOnlyConjunct {
	fn := v.fn
	if len(v.frame) == 0 {
		return nil
	}
	var found []entryOnlyConjunct
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			if v.speaksOfReturn(conjunct) {
				continue
			}
			// Results and the state on return are given, so that every
			// clause can be read here; whether one speaks of them is
			// decided above.
			changed := st.clone()
			results := make([]value, len(fn.results))
			for i, result := range fn.results {
				results[i] = v.unknown("out", result.Type(), changed)
			}
			before := &specEnv{v: v, sink: changed, fn: fn, args: v.entry, results: results, now: memory{}, post: memory{}, before: st.brk}
			then, err := v.resolverOf(c).Formula(conjunct, before)
			if err != nil {
				// The clause is read, and its fault reported, where it is
				// proved.
				continue
			}
			for _, t := range v.frame {
				v.havoc(changed, t, nil)
			}
			after := &specEnv{v: v, sink: changed, fn: fn, args: v.entry, results: results, now: changed.mem, post: changed.mem, before: st.brk}
			now, err := v.resolverOf(c).Formula(conjunct, after)
			if err != nil {
				continue
			}
			if v.attempt(changed, nil, logic.Iff(then, now)) != solver.Proved {
				found = append(found, entryOnlyConjunct{clause: c, text: c.text[conjunct.Start:conjunct.End], primed: primedExample(c.text, conjunct)})
			}
		}
	}
	return found
}

// entryOnlyConjunct is a conjunct of an Ensures that entryOnly refuses.
type entryOnlyConjunct struct {
	clause *clause
	text   string
	primed string // a path of it, as the value on return
}

// message says what is wrong with the conjunct of an Ensures of the
// function called name.
func (e entryOnlyConjunct) message(name string) string {
	whole := ""
	if e.text != e.clause.text {
		whole = fmt.Sprintf(", in %q,", e.clause.text)
	}
	return fmt.Sprintf("the Ensures clause %q%s names no result and nothing on return, so it speaks of the state when %s is called, "+
		"and it reads memory that %s may modify; write a prime for the value on return, as in %s, or move the clause to a Requires",
		e.text, whole, name, name, e.primed)
}

// speaksOfReturn reports whether a formula names a result of the function,
// has a primed path, or applies fresh, any of which speaks of the state on
// return. A name bound by a quantifier inside is not a result.
func (v *fnVerifier) speaksOfReturn(n *logic.Node) bool {
	var visit func(n *logic.Node, bound map[string]bool) bool
	visit = func(n *logic.Node, bound map[string]bool) bool {
		switch {
		case n.Primed:
			return true
		case n.Kind == logic.NCall && n.Name == "fresh":
			return true
		case n.Kind == logic.NIdent && !bound[n.Name]:
			if _, isResult := v.fn.resultNames[n.Name]; isResult {
				return true
			}
		case n.Kind == logic.NQuant:
			inner := map[string]bool{}
			for name := range bound {
				inner[name] = true
			}
			for _, name := range n.Vars {
				inner[name] = true
			}
			bound = inner
		}
		for _, kid := range n.Kids {
			if visit(kid, bound) {
				return true
			}
		}
		return false
	}
	return visit(n, map[string]bool{})
}

// primedExample writes the first path of a formula that reaches memory as
// the value on return: a field or an element, primed before its index,
// or failing that the first name.
func primedExample(text string, n *logic.Node) string {
	var path, name *logic.Node
	var visit func(n *logic.Node)
	visit = func(n *logic.Node) {
		if path != nil {
			return
		}
		switch n.Kind {
		case logic.NField, logic.NIndex:
			path = n
			return
		case logic.NIdent:
			if name == nil {
				name = n
			}
		}
		for _, kid := range n.Kids {
			visit(kid)
		}
	}
	visit(n)
	switch {
	case path != nil && path.Kind == logic.NIndex:
		base := path.Kids[0]
		return text[base.Start:base.End] + "'" + text[base.End:path.End]
	case path != nil:
		return text[path.Start:path.End] + "'"
	case name != nil:
		return text[name.Start:name.End] + "'"
	}
	return "p.x'"
}
