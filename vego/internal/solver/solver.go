// Package solver is the native deduction engine of vego. It proves
// verification conditions by refutation: the hypotheses together with the
// negated goal are shown to be unsatisfiable.
//
// The engine combines case splitting over the propositional structure,
// linear integer arithmetic by Fourier–Motzkin elimination, sequence axioms
// for reads over writes, instantiation of quantified facts at the terms that
// occur in the problem, and bounded unfolding of user-defined predicates.
// Every rule is sound, and the engine is deliberately incomplete: a failure
// to prove is reported as Unknown and never as a refutation.
package solver

import (
	"fmt"
	"maps"
	"math/big"
	"slices"
	"strconv"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Result is the outcome of a proof attempt.
type Result int

// Proof outcomes.
const (
	Unknown Result = iota
	Proved
)

// Options configures a proof attempt.
type Options struct {
	// Preds holds the definitions of the predicates that may occur.
	Preds map[string]*logic.PredDef
	// MaxSteps bounds the number of arithmetic feasibility checks, which
	// makes the outcome deterministic. Zero selects the default.
	MaxSteps int

	bigOnly bool // skip the 64-bit fast path of the arithmetic; for tests
}

const (
	defaultMaxSteps = 60000
	maxInstanceGen  = 3   // quantifier instances may build on instances this deep
	maxUnfoldGen    = 2   // predicate applications this deep are still unfolded
	maxInstances    = 500 // per branch
	maxAckermann    = 300 // per branch
	maxProducts     = 200 // per branch
)

// giveUp is panicked when the step budget is exhausted.
type giveUp struct{}

// Prove reports whether goal follows from the hypotheses.
func Prove(hyps []*logic.Term, goal *logic.Term, opts Options) (result Result) {
	p := &prover{
		bigOnly:  opts.bigOnly,
		preds:    opts.Preds,
		maxSteps: opts.MaxSteps,
		atomIDs:  map[string]int{},
		linCache: map[*logic.Term]poly{},
		bound:    map[*logic.Term]bool{},
		triggers: map[*logic.Term][]trigger{},
		bases:    map[int]string{},
	}
	if p.maxSteps == 0 {
		p.maxSteps = defaultMaxSteps
	}
	defer func() {
		switch r := recover().(type) {
		case nil:
		case giveUp, overflow:
			result = Unknown
		default:
			panic(r)
		}
	}()
	b := &branch{
		bools:    map[int]bool{},
		seen:     map[int]int{},
		monos:    map[string]bool{},
		inst:     map[string]bool{},
		unfolded: map[int]bool{},
		acked:    map[[2]int]bool{},
		dirty:    map[string]bool{},
	}
	for _, hyp := range hyps {
		p.add(b, hyp, 0)
	}
	p.add(b, logic.Not(goal), 0)
	if p.refute(b) {
		return Proved
	}
	return Unknown
}

type prover struct {
	bigOnly   bool // skip the 64-bit fast path; set by tests
	preds     map[string]*logic.PredDef
	steps     int
	maxSteps  int
	fresh     int
	atomIDs   map[string]int
	atomTerms []*logic.Term
	atomBound []bool
	linCache  map[*logic.Term]poly
	bound     map[*logic.Term]bool
	triggers  map[*logic.Term][]trigger
	bases     map[int]string
}

type clause struct {
	disj []*logic.Term
	gen  int
	// seen is set once every disjunct has been tested against the branch.
	seen bool
}

type quantified struct {
	fact *logic.Term
	gen  int
}

// branch is one case of the proof search: a conjunction of arithmetic
// literals, boolean literals, clauses still to be split, and quantified facts.
type branch struct {
	conflict  bool
	eqs       []poly // each = 0
	les       []poly // each <= 0
	bools     map[int]bool
	clauses   []clause
	foralls   []quantified
	seen      map[int]int // ground atom -> generation it appeared in
	monos     map[string]bool
	inst      map[string]bool
	unfolded  map[int]bool
	acked     map[[2]int]bool
	instances int
	products  int
	// dirty holds the unknowns of the arithmetic facts added since the
	// clauses were last tested against the branch.
	dirty map[string]bool
	// parts is the partition of the arithmetic facts, until one is added.
	parts *partition
}

// touch records that an arithmetic fact about the unknowns of pl was added.
func (b *branch) touch(pl poly) {
	b.parts = nil
	for mono := range pl.m {
		b.dirty[mono] = true
	}
}

func (b *branch) clone() *branch {
	c := *b
	c.eqs, c.les = slices.Clone(b.eqs), slices.Clone(b.les)
	c.clauses, c.foralls = slices.Clone(b.clauses), slices.Clone(b.foralls)
	c.bools, c.seen, c.monos = maps.Clone(b.bools), maps.Clone(b.seen), maps.Clone(b.monos)
	c.inst, c.unfolded, c.acked = maps.Clone(b.inst), maps.Clone(b.unfolded), maps.Clone(b.acked)
	c.dirty = maps.Clone(b.dirty)
	return &c
}

// hasBound reports whether a term mentions a bound variable, which makes it
// unusable as a ground fact.
func (p *prover) hasBound(t *logic.Term) bool {
	if t.Op == logic.OpBound {
		return true
	}
	if len(t.Args) == 0 {
		return false
	}
	if cached, ok := p.bound[t]; ok {
		return cached
	}
	result := slices.ContainsFunc(t.Args, p.hasBound)
	p.bound[t] = result
	return result
}

// reduce simplifies reads of constructed sequences and constant divisions when
// that can be decided syntactically. It returns t itself when nothing applies.
func (p *prover) reduce(t *logic.Term) *logic.Term {
	switch t.Op {
	case logic.OpSelect:
		seq, index := t.Args[0], t.Args[1]
		switch seq.Op {
		case logic.OpSelect:
			// The sequence is itself read out of a sequence of sequences.
			if inner := p.reduce(seq); inner != seq {
				return p.reduce(logic.Select(inner, index))
			}
			if hit, written, missed, ok := split(seq); ok {
				return logic.Ite(hit, p.reduce(logic.Select(written, index)), p.reduce(logic.Select(missed, index)))
			}
		case logic.OpFill:
			return seq.Args[1]
		case logic.OpSub:
			return p.reduce(logic.Select(seq.Args[0], logic.Add(seq.Args[1], index)))
		case logic.OpConcat:
			// Decide which half is read when the index is a constant
			// distance from the end of the first half.
			first := logic.Len(seq.Args[0])
			distance := p.lin(index).add(p.lin(first), -1)
			switch {
			case !distance.isConst():
				return t
			case distance.c.Sign() < 0:
				return p.reduce(logic.Select(seq.Args[0], index))
			}
			return p.reduce(logic.Select(seq.Args[1], logic.Sub(index, first)))
		case logic.OpStore, logic.OpPush:
			written := seq.Args[1]
			if seq.Op == logic.OpPush {
				written = logic.Len(seq.Args[0])
			}
			distance := p.lin(index).add(p.lin(written), -1)
			if !distance.isConst() {
				return t
			}
			if distance.c.Sign() == 0 {
				return p.reduce(seq.Args[len(seq.Args)-1])
			}
			return p.reduce(logic.Select(seq.Args[0], index))
		}
	case logic.OpIsNil:
		inner := p.reduce(t.Args[0])
		if inner.Op == logic.OpIte {
			return logic.Ite(inner.Args[0], p.reduce(logic.IsNil(inner.Args[1])), p.reduce(logic.IsNil(inner.Args[2])))
		}
		if inner != t.Args[0] {
			return p.reduce(logic.IsNil(inner))
		}
		// An error read after a write is the written error or the one that
		// was there, and is nil accordingly.
		if inner.Op == logic.OpSelect {
			if hit, written, missed, ok := split(inner); ok {
				return logic.Ite(hit, p.reduce(logic.IsNil(written)), p.reduce(logic.IsNil(missed)))
			}
		}
	case logic.OpLen:
		switch seq := t.Args[0]; seq.Op {
		case logic.OpSelect:
			if inner := p.reduce(seq); inner != seq {
				return p.reduce(logic.Len(inner))
			}
			if hit, written, missed, ok := split(seq); ok {
				return logic.Ite(hit, p.reduce(logic.Len(written)), p.reduce(logic.Len(missed)))
			}
		case logic.OpStore:
			return p.reduce(logic.Len(seq.Args[0]))
		case logic.OpFill:
			return seq.Args[0]
		case logic.OpPush:
			return logic.Add(logic.Len(seq.Args[0]), logic.IntLit(1))
		case logic.OpConcat:
			return logic.Add(logic.Len(seq.Args[0]), logic.Len(seq.Args[1]))
		case logic.OpSub:
			return logic.Sub(seq.Args[2], seq.Args[1])
		}
	case logic.OpDiv, logic.OpMod:
		a, b := p.lin(t.Args[0]), p.lin(t.Args[1])
		// Quo and Rem truncate toward zero, as Go's / and % do.
		if a.isConst() && b.isConst() && b.c.Sign() != 0 {
			if t.Op == logic.OpDiv {
				return logic.BigLit(new(big.Int).Quo(a.c, b.c))
			}
			return logic.BigLit(new(big.Int).Rem(a.c, b.c))
		}
	}
	return t
}

// split takes a read of an updated sequence whose index is not known to hit
// or miss the update, and returns the condition under which it hits, the
// value written, and the read of the sequence before the update. It is used
// for reads that yield a sequence, which cannot be given a name and an axiom
// the way a read of a number can.
func split(read *logic.Term) (hit, written, missed *logic.Term, ok bool) {
	seq, index := read.Args[0], read.Args[1]
	if seq.Op != logic.OpStore {
		return nil, nil, nil, false
	}
	return logic.Eq(index, seq.Args[1]), seq.Args[2], logic.Select(seq.Args[0], index), true
}

// lin converts an integer term into a polynomial over atoms. Arithmetic is
// expanded; every other integer term becomes an atom.
func (p *prover) lin(t *logic.Term) poly {
	if cached, ok := p.linCache[t]; ok {
		return cached
	}
	var result poly
	switch t.Op {
	case logic.OpIntLit:
		result = poly{c: t.Value()}
	case logic.OpAdd:
		result = p.lin(t.Args[0]).add(p.lin(t.Args[1]), 1)
	case logic.OpNeg:
		result = constPoly(0).add(p.lin(t.Args[0]), -1)
	case logic.OpMul:
		result = p.lin(t.Args[0]).mul(p.lin(t.Args[1]))
	default:
		if reduced := p.reduce(t); reduced != t {
			result = p.lin(reduced)
		} else {
			result = monomialPoly(strconv.Itoa(p.atom(t)))
		}
	}
	p.linCache[t] = result
	return result
}

// atom interns an irreducible term and returns its identifier. Terms that are
// equal up to arithmetic normalisation of their arguments share an atom.
func (p *prover) atom(t *logic.Term) int {
	key := p.key(t)
	if id, ok := p.atomIDs[key]; ok {
		return id
	}
	id := len(p.atomTerms)
	p.atomIDs[key] = id
	p.atomTerms = append(p.atomTerms, t)
	p.atomBound = append(p.atomBound, p.hasBound(t))
	return id
}

// key returns a canonical string for a term: integer terms are keyed by their
// polynomial, everything else structurally.
func (p *prover) key(t *logic.Term) string {
	switch t.Op {
	case logic.OpConst, logic.OpBound:
		return "$" + t.Name
	case logic.OpIntLit, logic.OpAdd, logic.OpNeg, logic.OpMul:
		return p.lin(t).key()
	}
	var b strings.Builder
	b.WriteString(strconv.Itoa(int(t.Op)))
	b.WriteString(t.Name)
	b.WriteByte('(')
	for _, arg := range t.Args {
		if arg.Sort.Numeric() {
			b.WriteString(p.lin(arg).key())
		} else {
			b.WriteString(p.key(arg))
		}
		b.WriteByte(',')
	}
	b.WriteByte(')')
	return b.String()
}

// polyTerm converts a polynomial back into a term.
func (p *prover) polyTerm(pl poly) *logic.Term {
	result := logic.BigLit(pl.c)
	for _, mono := range pl.monomials() {
		term := logic.BigLit(pl.m[mono])
		for _, id := range monomialAtoms(mono) {
			term = logic.Mul(term, p.atomTerms[id])
		}
		result = logic.Add(result, term)
	}
	return result
}

// nnf pushes negation down to the literals of a ground formula. Existential
// quantifiers are replaced by fresh constants; universal quantifiers are kept
// as facts to instantiate later. Negated integer comparisons are rewritten to
// positive ones, so the only negative literals left are boolean atoms.
func (p *prover) nnf(t *logic.Term, neg bool) *logic.Term {
	args := t.Args
	junction := func(conjunction bool, parts ...*logic.Term) *logic.Term {
		if conjunction {
			return logic.And(parts...)
		}
		return logic.Or(parts...)
	}
	switch t.Op {
	case logic.OpTrue, logic.OpFalse:
		return logic.BoolLit((t.Op == logic.OpTrue) != neg)
	case logic.OpAnd, logic.OpOr:
		parts := make([]*logic.Term, len(args))
		for i, arg := range args {
			parts[i] = p.nnf(arg, neg)
		}
		return junction((t.Op == logic.OpAnd) != neg, parts...)
	case logic.OpNot:
		return p.nnf(args[0], !neg)
	case logic.OpImplies:
		return junction(neg, p.nnf(args[0], !neg), p.nnf(args[1], neg))
	case logic.OpIff:
		forward := junction(neg, p.nnf(args[0], !neg), p.nnf(args[1], neg))
		backward := junction(neg, p.nnf(args[0], neg), p.nnf(args[1], !neg))
		return junction(!neg, forward, backward)
	case logic.OpIte:
		return logic.And(
			logic.Or(p.nnf(args[0], true), p.nnf(args[1], neg)),
			logic.Or(p.nnf(args[0], false), p.nnf(args[2], neg)),
		)
	case logic.OpForall, logic.OpExists:
		if (t.Op == logic.OpForall) != neg {
			if neg {
				return logic.Forall(args[0], logic.Not(args[1]))
			}
			return t
		}
		p.fresh++
		witness := logic.Const(fmt.Sprintf("%s!%d", args[0].Name, p.fresh), args[0].Sort)
		return p.nnf(logic.Subst(args[1], map[string]*logic.Term{args[0].Name: witness}), neg)
	case logic.OpEq:
		if neg {
			return logic.Or(logic.Lt(args[0], args[1]), logic.Lt(args[1], args[0]))
		}
		return t
	case logic.OpLe:
		if neg {
			return logic.Lt(args[1], args[0])
		}
		return t
	case logic.OpLt:
		if neg {
			return logic.Le(args[1], args[0])
		}
		return t
	}
	if reduced := p.reduce(t); reduced != t {
		return p.nnf(reduced, neg)
	}
	if neg {
		return logic.Not(t)
	}
	return t
}

// add records a formula as true in the branch.
func (p *prover) add(b *branch, f *logic.Term, gen int) {
	normal := p.nnf(f, false)
	p.scan(b, normal, gen)
	p.assert(b, normal, gen)
}

// assert distributes a formula in negation normal form over the branch state.
func (p *prover) assert(b *branch, f *logic.Term, gen int) {
	switch f.Op {
	case logic.OpTrue:
	case logic.OpFalse:
		b.conflict = true
	case logic.OpAnd:
		for _, arg := range f.Args {
			p.assert(b, arg, gen)
		}
	case logic.OpOr:
		b.clauses = append(b.clauses, clause{disj: f.Args, gen: gen})
	case logic.OpForall:
		b.foralls = append(b.foralls, quantified{f, gen})
	case logic.OpEq, logic.OpLe, logic.OpLt:
		pl, equality := p.constraint(f)
		switch {
		case !pl.isConst() && equality:
			b.eqs = append(b.eqs, pl)
			b.touch(pl)
		case !pl.isConst():
			b.les = append(b.les, pl)
			b.touch(pl)
		case pl.c.Sign() > 0 || (equality && pl.c.Sign() != 0):
			b.conflict = true
		}
	default:
		atom, positive := f, true
		if f.Op == logic.OpNot {
			atom, positive = f.Args[0], false
		}
		id := p.atom(atom)
		if previous, known := b.bools[id]; known && previous != positive {
			b.conflict = true
		}
		b.bools[id] = positive
	}
}

// constraint converts a positive arithmetic literal into "poly = 0" or
// "poly <= 0" form.
func (p *prover) constraint(f *logic.Term) (pl poly, equality bool) {
	pl = p.lin(f.Args[0]).add(p.lin(f.Args[1]), -1)
	if f.Op == logic.OpLt {
		pl = pl.add(constPoly(1), 1)
	}
	return pl, f.Op == logic.OpEq
}

// scan registers the ground atoms of a formula with the branch and adds the
// theory axioms that give those atoms their meaning.
func (p *prover) scan(b *branch, t *logic.Term, gen int) {
	if !p.hasBound(t) {
		switch t.Op {
		case logic.OpConst, logic.OpSelect, logic.OpLen, logic.OpDiv, logic.OpMod, logic.OpIte, logic.OpPred, logic.OpIsNil:
			if t.Sort.IsSeq() {
				// A sequence read out of a sequence of sequences has no
				// axioms of its own, but its index is one at which a fact
				// about the outer sequence matters.
				if t.Op == logic.OpSelect && p.reduce(t) == t {
					if _, known := b.seen[p.atom(t)]; !known {
						b.seen[p.atom(t)] = gen
					}
				}
				break
			}
			if reduced := p.reduce(t); reduced != t {
				p.scan(b, reduced, gen)
				return
			}
			id := p.atom(t)
			if previous, known := b.seen[id]; !known {
				b.seen[id] = gen
				p.axioms(b, t, gen)
			} else if gen < previous {
				b.seen[id] = gen
			}
		case logic.OpMul:
			p.productAxioms(b, t, gen)
		}
	}
	for _, arg := range t.Args {
		p.scan(b, arg, gen)
	}
}

// axioms adds the defining facts of a newly seen atom: lengths are
// non-negative, a read of an updated sequence sees either the written value or
// the old element, conditionals pick a branch, and division satisfies Go's
// truncated quotient-remainder law.
func (p *prover) axioms(b *branch, t *logic.Term, gen int) {
	zero := logic.IntLit(0)
	switch t.Op {
	case logic.OpLen:
		p.add(b, logic.Le(zero, t), gen)
	case logic.OpSelect:
		seq, index := t.Args[0], t.Args[1]
		if seq.Op == logic.OpConcat {
			first := logic.Len(seq.Args[0])
			inFirst := logic.Lt(index, first)
			p.add(b, logic.Implies(inFirst, logic.Eq(t, logic.Select(seq.Args[0], index))), gen)
			p.add(b, logic.Or(inFirst, logic.Eq(t, logic.Select(seq.Args[1], logic.Sub(index, first)))), gen)
			return
		}
		if seq.Op != logic.OpStore && seq.Op != logic.OpPush {
			return
		}
		written := seq.Args[1]
		if seq.Op == logic.OpPush {
			written = logic.Len(seq.Args[0])
		}
		hit := logic.Eq(index, written)
		p.add(b, logic.Implies(hit, logic.Eq(t, seq.Args[len(seq.Args)-1])), gen)
		p.add(b, logic.Or(hit, logic.Eq(t, logic.Select(seq.Args[0], index))), gen)
	case logic.OpIte:
		// A conditional formula is taken apart where it is asserted, and one
		// that yields a sequence never survives reduction.
		if t.Sort == logic.Bool || t.Sort.IsSeq() {
			return
		}
		p.add(b, logic.Implies(t.Args[0], logic.Eq(t, t.Args[1])), gen)
		p.add(b, logic.Or(t.Args[0], logic.Eq(t, t.Args[2])), gen)
	case logic.OpDiv, logic.OpMod:
		x, y := t.Args[0], t.Args[1]
		quotient, remainder := logic.Div(x, y), logic.Mod(x, y)
		b.seen[p.atom(quotient)], b.seen[p.atom(remainder)] = gen, gen
		positive, negative := logic.Lt(zero, y), logic.Lt(y, zero)
		law := logic.Eq(x, logic.Add(logic.Mul(y, quotient), remainder))
		p.add(b, logic.Implies(logic.Or(positive, negative), law), gen)
		within := func(lo, hi *logic.Term) *logic.Term { return logic.And(logic.Lt(lo, hi), logic.Le(zero, remainder)) }
		p.add(b, logic.Implies(logic.And(positive, logic.Le(zero, x)), within(remainder, y)), gen)
		p.add(b, logic.Implies(logic.And(negative, logic.Le(zero, x)), within(remainder, logic.Neg(y))), gen)
		below := func(lo *logic.Term) *logic.Term { return logic.And(logic.Lt(lo, remainder), logic.Le(remainder, zero)) }
		p.add(b, logic.Implies(logic.And(positive, logic.Le(x, zero)), below(logic.Neg(y))), gen)
		p.add(b, logic.Implies(logic.And(negative, logic.Le(x, zero)), below(y)), gen)
	}
}

// productAxioms adds sign rules for products of two atoms, the only
// non-linear reasoning the engine performs beyond polynomial normalisation.
func (p *prover) productAxioms(b *branch, t *logic.Term, gen int) {
	zero := logic.IntLit(0)
	for mono := range p.lin(t).m {
		ids := monomialAtoms(mono)
		if len(ids) != 2 || b.monos[mono] {
			continue
		}
		b.monos[mono] = true
		x, y := p.atomTerms[ids[0]], p.atomTerms[ids[1]]
		product := logic.Mul(x, y)
		if ids[0] == ids[1] {
			p.add(b, logic.Le(zero, product), gen)
			continue
		}
		for _, signs := range [][2]bool{{true, true}, {false, false}, {true, false}, {false, true}} {
			sign := func(positive bool, v *logic.Term) *logic.Term {
				if positive {
					return logic.Le(zero, v)
				}
				return logic.Le(v, zero)
			}
			premise := logic.And(sign(signs[0], x), sign(signs[1], y))
			p.add(b, logic.Implies(premise, sign(signs[0] == signs[1], product)), gen)
		}
	}
}

// falsified reports whether a formula in negation normal form contradicts the
// literals of the branch.
func (p *prover) falsified(b *branch, f *logic.Term) bool {
	switch f.Op {
	case logic.OpTrue, logic.OpForall:
		return false
	case logic.OpFalse:
		return true
	case logic.OpAnd:
		return slices.ContainsFunc(f.Args, func(arg *logic.Term) bool { return p.falsified(b, arg) })
	case logic.OpOr:
		return !slices.ContainsFunc(f.Args, func(arg *logic.Term) bool { return !p.falsified(b, arg) })
	case logic.OpEq, logic.OpLe, logic.OpLt:
		pl, equality := p.constraint(f)
		switch {
		case pl.isConst():
			return pl.c.Sign() > 0 || (equality && pl.c.Sign() != 0)
		}
		return p.contradicts(b, pl, equality)
	case logic.OpNot:
		positive, known := b.bools[p.atom(f.Args[0])]
		return known && positive
	}
	positive, known := b.bools[p.atom(f)]
	return known && !positive
}

// entailed reports whether a literal already follows from the branch, in
// which case a clause containing it carries no information.
func (p *prover) entailed(b *branch, f *logic.Term) bool {
	x := f.Args
	switch f.Op {
	case logic.OpTrue:
		return true
	case logic.OpEq:
		return p.falsified(b, logic.Lt(x[0], x[1])) && p.falsified(b, logic.Lt(x[1], x[0]))
	case logic.OpLe:
		return p.falsified(b, logic.Lt(x[1], x[0]))
	case logic.OpLt:
		return p.falsified(b, logic.Le(x[1], x[0]))
	case logic.OpNot:
		positive, known := b.bools[p.atom(x[0])]
		return known && !positive
	case logic.OpAnd, logic.OpOr, logic.OpForall, logic.OpFalse:
		return false
	}
	positive, known := b.bools[p.atom(f)]
	return known && positive
}

// propagate removes the disjuncts that the branch contradicts from every
// clause. A clause left with one disjunct is asserted, and a clause left with
// none closes the branch. It reports whether the branch learned anything.
//
// An arithmetic disjunct that was not contradicted before can only be
// contradicted now if a fact was added about its unknowns or about unknowns
// connected to them, so only those disjuncts are tested again.
func (p *prover) propagate(b *branch) bool {
	find := p.parts(b).find
	changed := map[string]bool{}
	for mono := range b.dirty {
		changed[find(mono)] = true
	}
	b.dirty = map[string]bool{}
	var stale func(d *logic.Term) bool
	stale = func(d *logic.Term) bool {
		switch d.Op {
		case logic.OpEq, logic.OpLe, logic.OpLt:
			pl, _ := p.constraint(d)
			for mono := range pl.m {
				if changed[find(mono)] {
					return true
				}
			}
			return pl.isConst()
		case logic.OpAnd, logic.OpOr:
			return slices.ContainsFunc(d.Args, stale)
		}
		return true
	}
	var kept, units []clause
	for _, c := range b.clauses {
		var live []*logic.Term
		for _, d := range c.disj {
			if (c.seen && !stale(d)) || !p.falsified(b, d) {
				live = append(live, d)
			}
		}
		switch len(live) {
		case 0:
			b.conflict = true
			return true
		case 1:
			units = append(units, clause{disj: live, gen: c.gen})
		default:
			kept = append(kept, clause{disj: live, gen: c.gen, seen: true})
		}
	}
	b.clauses = kept
	for _, unit := range units {
		p.assert(b, unit.disj[0], unit.gen)
	}
	return len(units) > 0
}

// refute reports whether the branch is unsatisfiable. It saturates the branch
// with unit propagation and theory expansion, then splits on the smallest
// remaining clause and requires every case to be refuted.
func (p *prover) refute(b *branch) bool {
	for {
		if b.conflict || p.infeasible(b) {
			return true
		}
		if !p.propagate(b) && !p.expand(b) {
			break
		}
	}
	chosen, ok := p.pick(b)
	if !ok {
		return false
	}
	var earlier []*logic.Term
	for _, d := range chosen.disj {
		next := b.clone()
		for _, e := range earlier {
			p.add(next, logic.Not(e), chosen.gen)
		}
		p.assert(next, d, chosen.gen)
		if !p.refute(next) {
			return false
		}
		if d.Op != logic.OpAnd && d.Op != logic.OpOr && d.Op != logic.OpForall {
			earlier = append(earlier, d)
		}
	}
	return true
}

// pick removes and returns the clause with the fewest disjuncts, discarding
// clauses that are already satisfied by an entailed literal.
func (p *prover) pick(b *branch) (clause, bool) {
	for len(b.clauses) > 0 {
		best := 0
		for i, c := range b.clauses {
			if len(c.disj) < len(b.clauses[best].disj) {
				best = i
			}
		}
		chosen := b.clauses[best]
		b.clauses = slices.Delete(b.clauses, best, best+1)
		satisfied := slices.ContainsFunc(chosen.disj, func(d *logic.Term) bool { return p.entailed(b, d) })
		if !satisfied {
			return chosen, true
		}
	}
	return clause{}, false
}

// expand adds facts that follow from the theories rather than from
// propagation: predicate unfoldings, quantifier instances, and functional
// consistency of sequence reads and predicate applications. It reports whether
// anything was added.
func (p *prover) expand(b *branch) bool {
	before := len(b.unfolded) + len(b.inst) + len(b.acked)
	atoms := slices.Sorted(maps.Keys(b.seen))
	for _, id := range slices.Sorted(maps.Keys(b.bools)) {
		t := p.atomTerms[id]
		def := p.preds[t.Name]
		if t.Op != logic.OpPred || def == nil || b.unfolded[id] || b.seen[id] >= maxUnfoldGen {
			continue
		}
		b.unfolded[id] = true
		bindings := map[string]*logic.Term{}
		for i, param := range def.Params {
			bindings[param.Name] = t.Args[i]
		}
		body := logic.Subst(def.Body, bindings)
		if !b.bools[id] {
			body = logic.Not(body)
		}
		p.add(b, body, b.seen[id]+1)
	}
	for i := 0; i < len(b.foralls); i++ {
		p.instantiate(b, i, atoms)
	}
	p.ackermann(b, atoms)
	p.products(b)
	return len(b.unfolded)+len(b.inst)+len(b.acked) != before
}

// products derives facts about products of two atoms, such as i*w, which the
// linear arithmetic treats as opaque. Two known inequalities f <= 0 and
// g <= 0 give f*g >= 0, and a known equality e = 0 gives e*y = 0 for any atom
// y. Expanding such a product yields a constraint that is linear in the
// products, so the ordinary elimination can use it. Only linear facts are
// multiplied, and a product is kept only when every product of atoms in it
// already occurs in the problem, which keeps the search goal-directed.
func (p *prover) products(b *branch) {
	if len(b.monos) == 0 {
		return
	}
	relevant := func(pl poly) bool {
		found := false
		for mono := range pl.m {
			if strings.Contains(mono, "*") {
				if !b.monos[mono] {
					return false
				}
				found = true
			}
		}
		return found
	}
	// A simple fact is linear and mentions at most three atoms.
	simple := func(pl poly) bool {
		for mono := range pl.m {
			if strings.Contains(mono, "*") {
				return false
			}
		}
		return len(pl.m) >= 1 && len(pl.m) <= 3
	}
	record := func(key string) bool {
		if b.inst[key] || b.products >= maxProducts {
			return false
		}
		b.inst[key] = true
		return true
	}
	// A factor of a product often has no sign fact of its own: from
	// 0 <= col < cols nothing says cols >= 0 directly. Such implied signs are
	// derived first and recorded as facts, so that they can be multiplied.
	atoms := map[string]bool{}
	for mono := range b.monos {
		for _, id := range monomialAtoms(mono) {
			atoms[strconv.Itoa(id)] = true
		}
	}
	for _, atom := range slices.Sorted(maps.Keys(atoms)) {
		for _, sign := range []int64{1, -1} {
			key := "sign|" + atom + "|" + strconv.FormatInt(sign, 10)
			// sign*x >= 0 holds when sign*x <= -1 is infeasible.
			opposite := constPoly(1).add(monomialPoly(atom), sign)
			if !b.inst[key] && p.contradicts(b, opposite, false) {
				b.inst[key] = true
				b.les = append(b.les, constPoly(0).add(monomialPoly(atom), -sign))
				b.touch(monomialPoly(atom))
			}
		}
	}
	// Of several constant bounds on one atom in one direction only the
	// tightest is multiplied; the others would add nothing but rows.
	tightest := map[string]poly{}
	var factors []poly
	for _, pl := range b.les {
		if !simple(pl) {
			continue
		}
		if len(pl.m) > 1 {
			factors = append(factors, pl)
			continue
		}
		for mono, coef := range pl.m {
			// pl is coef*x + c <= 0, which bounds x by -c/coef; with
			// coef = ±1 a larger constant is the tighter bound.
			side := mono + "|" + strconv.Itoa(coef.Sign())
			best, seen := tightest[side]
			if !coef.IsInt64() || abs(coef.Int64()) != 1 {
				factors = append(factors, pl)
			} else if !seen || pl.c.Cmp(best.c) > 0 {
				tightest[side] = pl
			}
		}
	}
	for _, side := range slices.Sorted(maps.Keys(tightest)) {
		factors = append(factors, tightest[side])
	}
	eqs := len(b.eqs)
	for i, first := range factors {
		for _, second := range factors[i:] {
			product := first.mul(second)
			if relevant(product) && record("product|"+first.key()+"|"+second.key()) {
				b.products++
				b.les = append(b.les, constPoly(0).add(product, -1))
				b.touch(product)
			}
		}
	}
	for i := 0; i < eqs; i++ {
		for _, atom := range slices.Sorted(maps.Keys(atoms)) {
			if !simple(b.eqs[i]) {
				break
			}
			product := b.eqs[i].mul(monomialPoly(atom))
			if relevant(product) && record("product|"+b.eqs[i].key()+"|="+atom) {
				b.products++
				b.eqs = append(b.eqs, product)
				b.touch(product)
			}
		}
	}
}

// trigger describes an argument position inside a quantified body where the
// bound variable x occurs as sign*x + rest. A ground atom with the same head
// and argument value g suggests the instance x = sign*(g - rest).
//
// base is set for a read of a sequence that does not itself depend on the
// bound variable; the trigger then matches reads of that sequence only. A
// fact about one slice is not instantiated at the indices of every other.
type trigger struct {
	head string
	base string
	arg  int
	sign int64
	rest poly
}

// head names the kind of atom a trigger matches. Reads indexed by a reference
// are kept apart from reads indexed by an integer, so that an address is never
// tried as a slice index.
func head(t *logic.Term) string {
	switch {
	case t.Op == logic.OpPred:
		return "pred " + t.Name
	case t.Args[1].Sort == logic.Ref:
		return "deref"
	}
	return "select"
}

// triggersOf finds the argument positions of sequence reads and predicate
// applications in the body of a quantified fact that pin down its variable.
func (p *prover) triggersOf(fact *logic.Term) []trigger {
	if cached, ok := p.triggers[fact]; ok {
		return cached
	}
	variable := strconv.Itoa(p.atom(fact.Args[0]))
	var found []trigger
	var walk func(t *logic.Term)
	walk = func(t *logic.Term) {
		// Ground atoms are recorded in reduced form, so a trigger has to
		// be read off the reduced form too: a read of a subsequence is a
		// read of the whole sequence at a shifted index.
		if reduced := p.reduce(t); reduced != t {
			walk(reduced)
			return
		}
		for _, arg := range t.Args {
			walk(arg)
		}
		if t.Op != logic.OpSelect && t.Op != logic.OpPred {
			return
		}
		for i, arg := range t.Args {
			if arg.Sort != logic.Int || (t.Op == logic.OpSelect && i != 1) {
				continue
			}
			pl := p.lin(arg)
			coef := pl.coef(variable)
			if !coef.IsInt64() || (coef.Int64() != 1 && coef.Int64() != -1) {
				continue
			}
			sign := coef.Int64()
			rest := pl.add(monomialPoly(variable), -sign)
			usable := true
			for mono := range rest.m {
				for _, id := range monomialAtoms(mono) {
					usable = usable && !p.atomBound[id]
				}
			}
			if usable {
				trig := trigger{head: head(t), arg: i, sign: sign, rest: rest}
				if t.Op == logic.OpSelect && !p.hasBound(t.Args[0]) {
					trig.base = p.key(t.Args[0])
				}
				found = append(found, trig)
			}
		}
	}
	walk(fact.Args[1])
	p.triggers[fact] = found
	return found
}

// baseKey returns the key of the sequence that a read atom reads.
func (p *prover) baseKey(id int) string {
	if key, ok := p.bases[id]; ok {
		return key
	}
	key := p.key(p.atomTerms[id].Args[0])
	p.bases[id] = key
	return key
}

// ends returns the first and the last value of the interval a quantified
// body is guarded by, as far as the guard states them: for a body of the
// form "lo <= x And x < hi -> ..." or "~(lo <= x And x < hi And ...)", lo
// and hi - 1.
func (p *prover) ends(variable, body *logic.Term) []poly {
	// A refuted "Exists x : lo <= x And x < hi And ..." is kept as the
	// negation of that conjunction.
	var guards []*logic.Term
	switch {
	case body.Op == logic.OpImplies:
		guards = logic.Conjuncts(body.Args[0])
	case body.Op == logic.OpNot:
		guards = logic.Conjuncts(body.Args[0])
	}
	var values []poly
	for _, guard := range guards {
		if guard.Op != logic.OpLe && guard.Op != logic.OpLt {
			continue
		}
		strict := int64(0)
		if guard.Op == logic.OpLt {
			strict = 1
		}
		switch low, high := guard.Args[0], guard.Args[1]; {
		case high == variable && !p.hasBound(low):
			values = append(values, p.lin(low).add(constPoly(strict), 1))
		case low == variable && !p.hasBound(high):
			values = append(values, p.lin(high).add(constPoly(strict), -1))
		}
	}
	return values
}

// instantiate adds instances of one quantified fact for the ground atoms that
// match its triggers. A fact without triggers is instantiated at every index
// that some sequence is read at.
func (p *prover) instantiate(b *branch, index int, atoms []int) {
	q := b.foralls[index]
	variable, body := q.fact.Args[0], q.fact.Args[1]
	triggers := p.triggersOf(q.fact)
	if len(triggers) == 0 {
		triggers = []trigger{{head: "select", arg: 1, sign: 1, rest: constPoly(0)}}
		// Nothing in the body says where the fact matters, so the ends of
		// the interval it ranges over are tried as well.
		for _, value := range p.ends(variable, body) {
			key := strconv.Itoa(index) + "|" + value.key()
			if b.inst[key] || b.instances >= maxInstances || q.gen+1 > maxInstanceGen {
				continue
			}
			b.inst[key] = true
			b.instances++
			p.add(b, logic.Subst(body, map[string]*logic.Term{variable.Name: p.polyTerm(value)}), q.gen+1)
		}
	}
	for _, id := range atoms {
		t := p.atomTerms[id]
		gen := max(q.gen, b.seen[id]) + 1
		if (t.Op != logic.OpSelect && t.Op != logic.OpPred) || gen > maxInstanceGen {
			continue
		}
		for _, trig := range triggers {
			if trig.head != head(t) || b.instances >= maxInstances || (trig.base != "" && trig.base != p.baseKey(id)) {
				continue
			}
			value := p.lin(t.Args[trig.arg]).add(trig.rest, -1)
			if trig.sign < 0 {
				value = constPoly(0).add(value, -1)
			}
			key := strconv.Itoa(index) + "|" + value.key()
			if b.inst[key] {
				continue
			}
			b.inst[key] = true
			b.instances++
			p.add(b, logic.Subst(body, map[string]*logic.Term{variable.Name: p.polyTerm(value)}), gen)
		}
	}
}

// indices flattens an atom into the group of atoms it must be consistent
// with and the numeric arguments that tell the atoms of a group apart. A read
// of a sequence that was itself read out of a sequence of sequences has both
// indices as arguments.
func (p *prover) indices(t *logic.Term) (group string, args []*logic.Term) {
	var b strings.Builder
	if t.Op == logic.OpPred {
		b.WriteString(head(t))
		for _, arg := range t.Args {
			if arg.Sort.Numeric() {
				args = append(args, arg)
			} else {
				b.WriteString(p.key(arg))
			}
			b.WriteByte(',')
		}
		return b.String(), args
	}
	base := t
	for base.Op == logic.OpSelect {
		args = append(args, base.Args[1])
		base = base.Args[0]
	}
	b.WriteString("select ")
	b.WriteString(strconv.Itoa(len(args)))
	b.WriteString(p.key(base))
	return b.String(), args
}

// ackermann adds functional consistency: two reads of the same sequence, or
// two applications of the same predicate, agree whenever their numeric
// arguments are equal.
func (p *prover) ackermann(b *branch, atoms []int) {
	groups := map[string][]int{}
	for _, id := range atoms {
		t := p.atomTerms[id]
		if (t.Op != logic.OpSelect && t.Op != logic.OpPred) || t.Sort.IsSeq() {
			continue
		}
		group, _ := p.indices(t)
		groups[group] = append(groups[group], id)
	}
	names := slices.Sorted(maps.Keys(groups))
	for _, name := range names {
		ids := groups[name]
		for i, first := range ids {
			for _, second := range ids[i+1:] {
				pair := [2]int{first, second}
				if b.acked[pair] || len(b.acked) >= maxAckermann {
					continue
				}
				b.acked[pair] = true
				p.consistency(b, p.atomTerms[first], p.atomTerms[second], max(b.seen[first], b.seen[second]))
			}
		}
	}
}

// consistency asserts that x and y agree unless some numeric argument differs.
// Nothing is added when two arguments differ by a non-zero constant.
func (p *prover) consistency(b *branch, x, y *logic.Term, gen int) {
	_, xs := p.indices(x)
	_, ys := p.indices(y)
	var disjuncts []*logic.Term
	for i, arg := range xs {
		other := ys[i]
		distance := p.lin(arg).add(p.lin(other), -1)
		if distance.isConst() {
			if distance.c.Sign() != 0 {
				return
			}
			continue
		}
		disjuncts = append(disjuncts, logic.Lt(arg, other), logic.Lt(other, arg))
	}
	disjuncts = append(disjuncts, logic.Eq(x, y))
	p.add(b, logic.Or(disjuncts...), gen)
}
