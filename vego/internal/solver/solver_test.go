package solver

import (
	"math"
	"math/rand/v2"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// seqValue is the model of a sequence used to evaluate terms: a length and a
// total function from indices to elements, as the sequence axioms assume.
type seqValue struct {
	length int64
	at     func(index int64) int64
}

func (s seqValue) with(i, v int64) seqValue {
	return seqValue{s.length, func(index int64) int64 {
		if index == i {
			return v
		}
		return s.at(index)
	}}
}

type model struct {
	ints map[string]int64
	seqs map[string]seqValue
	// maps holds the sequences of sequences, as total functions of the index.
	maps map[string]func(index int64) seqValue
}

// table evaluates a sequence of sequences.
func (m model) table(t *logic.Term) func(index int64) seqValue {
	if t.Op == logic.OpConst {
		return m.maps[t.Name]
	}
	if t.Op != logic.OpStore {
		panic("unexpected sequence of sequences " + t.String())
	}
	base, written := m.table(t.Args[0]), m.seq(t.Args[2])
	at, ok := m.eval(t.Args[1])
	if !ok {
		panic(divisionByZero{})
	}
	return func(index int64) seqValue {
		if index == at {
			return written
		}
		return base(index)
	}
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
		return m.seq(t.Args[0]).at(arg(1)), true
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
	case logic.OpSelect:
		return m.table(t.Args[0])(value(1))
	case logic.OpStore:
		return m.seq(t.Args[0]).with(value(1), value(2))
	case logic.OpPush:
		base := m.seq(t.Args[0])
		pushed := base.with(base.length, value(1))
		pushed.length++
		return pushed
	case logic.OpConcat:
		first, second := m.seq(t.Args[0]), m.seq(t.Args[1])
		return seqValue{first.length + second.length, func(index int64) int64 {
			if index < first.length {
				return first.at(index)
			}
			return second.at(index - first.length)
		}}
	case logic.OpSub:
		whole, lo := m.seq(t.Args[0]), value(1)
		return seqValue{value(2) - lo, func(index int64) int64 { return whole.at(lo + index) }}
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

// table builds a sequence of sequences: a base, possibly with some of its
// sequences replaced, which is the shape memory has in the verifier.
func (g *generator) table(depth int) *logic.Term {
	if depth > 0 && g.rng.IntN(2) == 0 {
		return logic.Store(g.table(depth-1), g.intTerm(0), g.seq(depth-1))
	}
	return logic.Const("M", logic.SeqOf(logic.IntSeq))
}

func (g *generator) seq(depth int) *logic.Term {
	base := logic.Const("A", logic.IntSeq)
	switch {
	case g.rng.IntN(6) == 0:
		return logic.Select(g.table(depth), g.intTerm(0))
	case depth > 0 && g.rng.IntN(4) == 0:
		return logic.Store(g.seq(depth-1), g.intTerm(depth-1), g.intTerm(depth-1))
	case depth > 0 && g.rng.IntN(8) == 0:
		return logic.Push(g.seq(depth-1), g.intTerm(depth-1))
	case depth > 0 && g.rng.IntN(8) == 0:
		return logic.Concat(g.seq(depth-1), g.seq(depth-1))
	case depth > 0 && g.rng.IntN(8) == 0:
		return logic.Subseq(g.seq(depth-1), g.intTerm(0), g.intTerm(0))
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
		switch g.rng.IntN(13) {
		case 0, 1:
			return logic.Le(a, b)
		case 2, 3:
			return logic.Lt(a, b)
		case 4, 5:
			return logic.Eq(a, b)
		case 6:
			return g.readOverWrite()
		case 7:
			return g.boundedProduct()
		case 8:
			return g.joinedOrCut()
		case 9, 10:
			return g.nestedRead()
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

// nestedRead states a fact about a sequence read out of a sequence of
// sequences: that a read of an updated table sees the written sequence or the
// old one, or that two reads agree. Each is valid only for the right relation
// between the indices, and the guard is sometimes missing or reversed.
func (g *generator) nestedRead() *logic.Term {
	table := g.table(1)
	i, j, k, l := g.intTerm(0), g.intTerm(0), g.intTerm(0), g.intTerm(0)
	guarded := func(same, fact *logic.Term) *logic.Term {
		switch g.rng.IntN(4) {
		case 0:
			return logic.Implies(same, fact)
		case 1:
			return logic.Implies(logic.Not(same), fact)
		}
		return fact
	}
	if g.rng.IntN(3) == 0 {
		// Two reads of one table agree when both indices do.
		same := []*logic.Term{logic.Eq(i, j), logic.Eq(k, l), logic.And(logic.Eq(i, j), logic.Eq(k, l))}[g.rng.IntN(3)]
		return guarded(same, logic.Eq(logic.Select(logic.Select(table, i), k), logic.Select(logic.Select(table, j), l)))
	}
	written := g.seq(1)
	row := logic.Select(logic.Store(table, i, written), j)
	old := logic.Select(table, j)
	expected := []*logic.Term{written, old}[g.rng.IntN(2)]
	if g.rng.IntN(3) == 0 {
		return guarded(logic.Eq(i, j), logic.Eq(logic.Len(row), logic.Len(expected)))
	}
	return guarded(logic.Eq(i, j), logic.Eq(logic.Select(row, k), logic.Select(expected, k)))
}

// joinedOrCut states a fact about the length or an element of a
// concatenation or a subsequence. About half of the generated facts are the
// true law and the rest are off by one or read the wrong half.
func (g *generator) joinedOrCut() *logic.Term {
	s, t := g.seq(1), g.seq(1)
	j, lo, hi := g.intTerm(0), g.intTerm(0), g.intTerm(0)
	slack := logic.IntLit(int64(g.rng.IntN(3) / 2))
	joined, cut := logic.Concat(s, t), logic.Subseq(s, lo, hi)
	inFirst := logic.Lt(j, logic.Len(s))
	switch g.rng.IntN(8) {
	case 6:
		// Reads at a fixed distance from the seam between the halves.
		at := logic.Add(logic.Len(s), logic.IntLit(int64(g.rng.IntN(3)-1)))
		half := []*logic.Term{logic.Select(s, at), logic.Select(t, logic.Sub(at, logic.Len(s)))}[g.rng.IntN(2)]
		return logic.Eq(logic.Select(joined, at), half)
	case 7:
		return logic.Eq(logic.Select(cut, j), logic.Select(s, j))
	case 0:
		return logic.Eq(logic.Len(joined), logic.Add(logic.Add(logic.Len(s), logic.Len(t)), slack))
	case 1:
		return logic.Implies(inFirst, logic.Eq(logic.Select(joined, j), logic.Select(s, logic.Add(j, slack))))
	case 2:
		second := logic.Select(t, logic.Add(logic.Sub(j, logic.Len(s)), slack))
		return logic.Implies(logic.Not(inFirst), logic.Eq(logic.Select(joined, j), second))
	case 3:
		return logic.Eq(logic.Select(joined, j), logic.Select([]*logic.Term{s, t}[g.rng.IntN(2)], j))
	case 4:
		return logic.Eq(logic.Len(cut), logic.Add(logic.Sub(hi, lo), slack))
	}
	return logic.Eq(logic.Select(cut, j), logic.Select(s, logic.Add(logic.Add(lo, j), slack)))
}

// boundedProduct bounds a product of two variables from bounds on its
// factors. The claimed bound is sometimes exact, sometimes one off in either
// direction, and the factor bounds are sometimes symbolic, so that a wrong
// rule for multiplying inequalities proves something false.
func (g *generator) boundedProduct() *logic.Term {
	x, y := g.vars[g.rng.IntN(len(g.vars))], g.vars[g.rng.IntN(len(g.vars))]
	lit := func(n int) *logic.Term { return logic.IntLit(int64(n)) }
	loX, hiX, loY, hiY := g.rng.IntN(3)-1, g.rng.IntN(3), g.rng.IntN(3)-1, g.rng.IntN(3)
	bounds := []*logic.Term{logic.Le(lit(loX), x), logic.Le(x, lit(hiX)), logic.Le(lit(loY), y)}
	product := logic.Mul(x, y)
	if g.rng.IntN(3) == 0 {
		z := g.vars[g.rng.IntN(len(g.vars))]
		bounds = append(bounds, logic.Le(x, z))
		claim := logic.Le(product, logic.Add(logic.Mul(z, y), lit(g.rng.IntN(3)-1)))
		return logic.Implies(logic.And(bounds...), claim)
	}
	bounds = append(bounds, logic.Le(y, lit(hiY)))
	slack := g.rng.IntN(3) - 1
	if g.rng.IntN(2) == 0 {
		return logic.Implies(logic.And(bounds...), logic.Le(product, lit(hiX*hiY+slack)))
	}
	return logic.Implies(logic.And(bounds...), logic.Le(lit(loX*loY+slack), product))
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
						seqs: map[string]seqValue{"A": {shape % 4, func(i int64) int64 { return (shape%3 + i*i) % 3 }}},
						maps: map[string]func(int64) seqValue{"M": func(r int64) seqValue {
							// Rows differ in length and content, and some
							// rows coincide.
							row := (r*r + shape) % 3
							return seqValue{(row + shape/4) % 3, func(i int64) int64 { return (row*i + shape/6) % 3 }}
						}},
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
	for i := range 4000 {
		g := &generator{rng: rng, vars: []*logic.Term{
			logic.Const("x", logic.Int), logic.Const("y", logic.Int), logic.Const("z", logic.Int),
		}}
		var hyps []*logic.Term
		for range rng.IntN(4) {
			hyps = append(hyps, g.formula(2))
		}
		goal := g.formula(2 + rng.IntN(2))
		// Every fourth problem runs on the arbitrary-precision arithmetic
		// alone, which must reach the same answers as the 64-bit path.
		opts := Options{MaxSteps: 600, bigOnly: i%4 == 0}
		result := Prove(hyps, goal, opts)
		if opts.bigOnly && result != Prove(hyps, goal, Options{MaxSteps: 600}) {
			t.Fatalf("problem %d: the two arithmetic paths disagree\nhyps: %v\ngoal: %v", i, hyps, goal)
		}
		if result != Proved {
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

// TestExtremeCoefficients checks goals that are false but whose
// refutation search passes through values at the edge of the 64-bit range,
// where a wrapped negation or rounding step once reversed an inequality.
func TestExtremeCoefficients(t *testing.T) {
	x := logic.Const("x", logic.Int)
	zero := logic.IntLit(0)
	least := logic.IntLit(math.MinInt64)
	most := logic.IntLit(math.MaxInt64)
	tests := []struct {
		name string
		hyp  *logic.Term
	}{
		{"smallest coefficient", logic.Le(logic.Mul(least, x), zero)},
		{"smallest constant", logic.Le(logic.Add(logic.Mul(logic.IntLit(2), x), least), zero)},
		{"largest constant", logic.Le(logic.Mul(logic.IntLit(2), x), most)},
		{"largest coefficient", logic.Le(zero, logic.Mul(most, x))},
		{"equality with smallest coefficient", logic.Eq(logic.Mul(least, x), logic.Mul(least, logic.IntLit(1)))},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// Every hypothesis holds for x = 1, so x <= 0 does not follow.
			if Prove([]*logic.Term{test.hyp}, logic.Le(x, zero), Options{}) == Proved {
				t.Fatalf("proved x <= 0 from %v, which x = 1 satisfies", test.hyp)
			}
		})
	}
}

// TestNilThroughMemory checks that whether an error read from memory is nil
// follows the write it was read after: the same reference sees the written
// error, and another reference sees what was there before.
func TestNilThroughMemory(t *testing.T) {
	memory := logic.Const("M", logic.SeqOf(logic.Err))
	p, q := logic.Const("p", logic.Ref), logic.Const("q", logic.Ref)
	failed := logic.Const("failed", logic.Err)
	written := logic.Store(memory, p, logic.NilErr())
	read := logic.IsNil(logic.Select(written, q))
	tests := []struct {
		name string
		hyps []*logic.Term
		goal *logic.Term
		want Result
	}{
		{"same reference sees the nil written", []*logic.Term{logic.Eq(p, q)}, read, Proved},
		{"other reference sees the old error", []*logic.Term{logic.Ne(p, q), logic.Not(logic.IsNil(logic.Select(memory, q)))}, logic.Not(read), Proved},
		{"unknown reference may see either", []*logic.Term{logic.Not(logic.IsNil(logic.Select(memory, q)))}, read, Unknown},
		{"unknown reference may see the old error", []*logic.Term{logic.Not(logic.IsNil(logic.Select(memory, q)))}, logic.Not(read), Unknown},
		{
			"a written error that is not nil is not nil when read back",
			[]*logic.Term{logic.Not(logic.IsNil(failed))},
			logic.Not(logic.IsNil(logic.Select(logic.Store(memory, p, failed), p))), Proved,
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got := Prove(test.hyps, test.goal, Options{})

			if got != test.want {
				t.Fatalf("Prove(%v, %v) = %v, want %v", test.hyps, test.goal, got, test.want)
			}
		})
	}
}
