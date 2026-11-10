package solver

import (
	"math/rand/v2"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// seqValue is the model of a sequence used to evaluate terms: a length and a
// total function from indices to elements, as the sequence axioms assume.
type seqValue struct {
	length int64
	base   int64
	writes map[int64]int64
}

func (s seqValue) with(i, v int64) seqValue {
	writes := map[int64]int64{i: v}
	for k, old := range s.writes {
		if k != i {
			writes[k] = old
		}
	}
	return seqValue{s.length, s.base, writes}
}

type model struct {
	ints map[string]int64
	seqs map[string]seqValue
}

// eval computes the value of a ground term in a model. Booleans are 0 and 1.
// The second result is false when the term divides by zero, in which case the
// assignment says nothing about the logic.
func (m model) eval(t *logic.Term) (int64, bool) {
	arg := func(i int) int64 {
		v, ok := m.eval(t.Args[i])
		if !ok {
			panic(divisionByZero{})
		}
		return v
	}
	truth := func(b bool) (int64, bool) {
		if b {
			return 1, true
		}
		return 0, true
	}
	switch t.Op {
	case logic.OpIntLit:
		return t.Val, true
	case logic.OpTrue:
		return 1, true
	case logic.OpFalse:
		return 0, true
	case logic.OpConst, logic.OpBound:
		return m.ints[t.Name], true
	case logic.OpAdd:
		return arg(0) + arg(1), true
	case logic.OpMul:
		return arg(0) * arg(1), true
	case logic.OpNeg:
		return -arg(0), true
	case logic.OpDiv, logic.OpMod:
		if arg(1) == 0 {
			return 0, false
		}
		if t.Op == logic.OpDiv {
			return arg(0) / arg(1), true
		}
		return arg(0) % arg(1), true
	case logic.OpLen:
		return m.seq(t.Args[0]).length, true
	case logic.OpSelect:
		s, i := m.seq(t.Args[0]), arg(1)
		if v, ok := s.writes[i]; ok {
			return v, true
		}
		return (s.base + i*i) % 3, true
	case logic.OpIte:
		if arg(0) == 1 {
			return arg(1), true
		}
		return arg(2), true
	case logic.OpEq, logic.OpIff:
		return truth(arg(0) == arg(1))
	case logic.OpLe:
		return truth(arg(0) <= arg(1))
	case logic.OpLt:
		return truth(arg(0) < arg(1))
	case logic.OpNot:
		return truth(arg(0) == 0)
	case logic.OpImplies:
		return truth(arg(0) == 0 || arg(1) == 1)
	case logic.OpAnd, logic.OpOr:
		for i := range t.Args {
			if (arg(i) == 1) == (t.Op == logic.OpOr) {
				return truth(t.Op == logic.OpOr)
			}
		}
		return truth(t.Op == logic.OpAnd)
	case logic.OpForall, logic.OpExists:
		// Generated quantifiers range over [-2, 4], which covers every
		// index the generator can produce a bound for.
		for x := int64(-2); x <= 4; x++ {
			m.ints[t.Args[0].Name] = x
			if (arg(1) == 1) == (t.Op == logic.OpExists) {
				return truth(t.Op == logic.OpExists)
			}
		}
		return truth(t.Op == logic.OpForall)
	}
	panic("unexpected term " + t.String())
}

type divisionByZero struct{}

func (m model) seq(t *logic.Term) seqValue {
	value := func(i int) int64 {
		v, ok := m.eval(t.Args[i])
		if !ok {
			panic(divisionByZero{})
		}
		return v
	}
	switch t.Op {
	case logic.OpConst:
		return m.seqs[t.Name]
	case logic.OpStore:
		return m.seq(t.Args[0]).with(value(1), value(2))
	case logic.OpPush:
		base := m.seq(t.Args[0])
		pushed := base.with(base.length, value(1))
		pushed.length++
		return pushed
	}
	panic("unexpected sequence " + t.String())
}

// generator builds random formulas over a few integers, one boolean, and one
// sequence. Quantifiers are bounded so that they can be evaluated exactly.
type generator struct {
	rng   *rand.Rand
	bound int
	vars  []*logic.Term
}

func (g *generator) seq(depth int) *logic.Term {
	base := logic.Const("A", logic.IntSeq)
	switch {
	case depth > 0 && g.rng.IntN(4) == 0:
		return logic.Store(g.seq(depth-1), g.intTerm(depth-1), g.intTerm(depth-1))
	case depth > 0 && g.rng.IntN(8) == 0:
		return logic.Push(g.seq(depth-1), g.intTerm(depth-1))
	}
	return base
}

func (g *generator) intTerm(depth int) *logic.Term {
	if depth <= 0 || g.rng.IntN(3) == 0 {
		if g.rng.IntN(3) == 0 {
			return logic.IntLit(int64(g.rng.IntN(5) - 1))
		}
		return g.vars[g.rng.IntN(len(g.vars))]
	}
	a, b := g.intTerm(depth-1), g.intTerm(depth-1)
	switch g.rng.IntN(12) {
	case 0, 1, 2:
		return logic.Add(a, b)
	case 3, 4:
		return logic.Sub(a, b)
	case 5:
		return logic.Mul(a, b)
	case 6:
		return logic.Div(a, b)
	case 7:
		return logic.Mod(a, b)
	case 8:
		return logic.Len(g.seq(depth - 1))
	case 9:
		return logic.Ite(g.formula(depth-1), a, b)
	}
	return logic.Select(g.seq(depth-1), a)
}

func (g *generator) formula(depth int) *logic.Term {
	if depth <= 0 || g.rng.IntN(3) == 0 {
		a, b := g.intTerm(depth), g.intTerm(depth)
		switch g.rng.IntN(9) {
		case 0, 1:
			return logic.Le(a, b)
		case 2, 3:
			return logic.Lt(a, b)
		case 4, 5:
			return logic.Eq(a, b)
		case 6, 7:
			return g.readOverWrite()
		}
		return logic.Const("p", logic.Bool)
	}
	a, b := g.formula(depth-1), g.formula(depth-1)
	switch g.rng.IntN(8) {
	case 0, 1:
		return logic.And(a, b)
	case 2:
		return logic.Or(a, b)
	case 3:
		return logic.Not(a)
	case 4, 5:
		return logic.Implies(a, b)
	case 6:
		return logic.Iff(a, b)
	}
	g.bound++
	x := logic.Bound("x#"+string(rune('a'+g.bound%26))+string(rune('a'+g.bound/26%26)), logic.Int)
	saved := g.vars
	g.vars = append(append([]*logic.Term(nil), g.vars...), x)
	// The upper bound never exceeds 4 in any generated model.
	lo, hi := logic.IntLit(int64(g.rng.IntN(3)-1)), logic.IntLit(int64(g.rng.IntN(4)))
	if g.rng.IntN(2) == 0 {
		hi = logic.Len(logic.Const("A", logic.IntSeq))
	}
	body := g.formula(depth - 1)
	g.vars = saved
	guard := logic.And(logic.Le(lo, x), logic.Lt(x, hi))
	if g.rng.IntN(2) == 0 {
		return logic.Forall(x, logic.Implies(guard, body))
	}
	return logic.Exists(x, logic.And(guard, body))
}

// readOverWrite relates a read of an updated sequence to the written value
// or to the old element. Such facts are valid only for the right index
// relationship, which makes them a sharp test of the sequence axioms.
func (g *generator) readOverWrite() *logic.Term {
	base := g.seq(1)
	i, j, v := g.intTerm(0), g.intTerm(0), g.intTerm(0)
	updated, written := logic.Store(base, i, v), i
	if g.rng.IntN(4) == 0 {
		updated, written = logic.Push(base, v), logic.Len(base)
	}
	expected := []*logic.Term{v, logic.Select(base, j)}[g.rng.IntN(2)]
	fact := logic.Eq(logic.Select(updated, j), expected)
	switch g.rng.IntN(4) {
	case 0:
		return logic.Implies(logic.Eq(written, j), fact)
	case 1:
		return logic.Implies(logic.Ne(written, j), fact)
	}
	return fact
}

// counterexample searches small models for one that satisfies every
// hypothesis and falsifies the goal.
func counterexample(hyps []*logic.Term, goal *logic.Term) (found bool, description model) {
	holds := func(m model, t *logic.Term) (result, defined bool) {
		defer func() {
			if r := recover(); r != nil {
				if _, ok := r.(divisionByZero); !ok {
					panic(r)
				}
				defined = false
			}
		}()
		v, ok := m.eval(t)
		return v == 1, ok
	}
	for x := int64(-2); x <= 2; x++ {
		for y := int64(-2); y <= 2; y++ {
			for z := int64(-1); z <= 1; z++ {
				for shape := int64(0); shape < 12; shape++ {
					m := model{
						ints: map[string]int64{"x": x, "y": y, "z": z, "p": shape % 2},
						seqs: map[string]seqValue{"A": {length: shape % 4, base: shape % 3}},
					}
					refutes := true
					for _, hyp := range hyps {
						if ok, defined := holds(m, hyp); !defined || !ok {
							refutes = false
							break
						}
					}
					if !refutes {
						continue
					}
					if ok, defined := holds(m, goal); defined && !ok {
						return true, m
					}
				}
			}
		}
	}
	return false, model{}
}

// TestProveIsSound checks the one property the engine must never violate: a
// proved goal holds in every model of the hypotheses. Random problems are
// proved and then evaluated exhaustively over small models.
func TestProveIsSound(t *testing.T) {
	rng := rand.New(rand.NewPCG(1, 2))
	proved := 0
	for i := range 5000 {
		g := &generator{rng: rng, vars: []*logic.Term{
			logic.Const("x", logic.Int), logic.Const("y", logic.Int), logic.Const("z", logic.Int),
		}}
		var hyps []*logic.Term
		for range rng.IntN(4) {
			hyps = append(hyps, g.formula(2))
		}
		goal := g.formula(2 + rng.IntN(2))
		if Prove(hyps, goal, Options{MaxSteps: 600}) != Proved {
			continue
		}
		proved++
		if found, m := counterexample(hyps, goal); found {
			t.Fatalf("problem %d: proved a goal that fails\nhyps: %v\ngoal: %v\nmodel: %v", i, hyps, goal, m)
		}
	}
	if proved < 300 {
		t.Fatalf("only %d random problems were proved; the test has lost its power", proved)
	}
	t.Logf("proved %d random problems, all confirmed by exhaustive evaluation", proved)
}
