package solver

import (
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"os"
	"slices"
	"strings"
	"sync"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// seqValue is the model of a sequence used to evaluate terms: a length and a
// total function from indices to elements, as the sequence axioms assume.
// A sequence built with a negative length is empty.
type seqValue struct {
	length int64
	at     func(index int64) int64
}

// spliced is what Splice means: as long as whole, inside's elements from
// lo up to hi, and whole's everywhere else.
func spliced(whole, inside seqValue, lo, hi int64) seqValue {
	return seqValue{whole.length, func(index int64) int64 {
		if lo <= index && index < hi {
			return inside.at(index)
		}
		return whole.at(index)
	}}
}

func (s seqValue) with(i, v int64) seqValue {
	return seqValue{s.length, func(index int64) int64 {
		if index == i {
			return v
		}
		return s.at(index)
	}}
}

// undefined is panicked when a model gives a term no value that the test can
// compare with the logic: a number outside 64 bits, a sequence too long to
// number, or a quantifier over all integers that a finite search leaves open.
// Such a model says nothing about the problem and is passed over.
type undefined struct{}

// plus adds two numbers of a model, which are mathematical integers.
func plus(a, b int64) int64 {
	c := a + b
	if b != 0 && (c > a) != (b > 0) {
		panic(undefined{})
	}
	return c
}

// times multiplies two numbers of a model, which are mathematical integers.
func times(a, b int64) int64 {
	product := new(big.Int).Mul(big.NewInt(a), big.NewInt(b))
	if !product.IsInt64() {
		panic(undefined{})
	}
	return product.Int64()
}

type model struct {
	// ints holds the integers, the booleans, the references, and the
	// errors, each error as a number that is zero exactly for nil.
	ints map[string]int64
	seqs map[string]seqValue
	// maps holds the sequences of sequences, as total functions of the index.
	maps map[string]func(index int64) seqValue
	// keys numbers the sequences met so far by their contents, which is a
	// function that tells exactly the equal sequences apart from the rest.
	keys map[string]int64
	// preds holds the definitions of the predicates.
	preds map[string]*logic.PredDef
	// wild selects one of a few unrelated meanings for division by zero,
	// which the logic leaves open, and divided records that one was used.
	wild    int64
	divided *bool
	// relation selects what errors.Is reports for two errors, which the
	// logic leaves open: equality, inequality, or a fixed table that is
	// neither.
	relation int64
}

// is says whether errors.Is reports true for two errors of a model.
func (m model) is(err, target int64) bool {
	switch m.relation {
	case 0:
		return err == target
	case 1:
		return err != target
	}
	return (err*2+target*3)%4 < 2
}

// key returns the number of a sequence.
func (m model) key(s seqValue) int64 {
	if s.length > 16 {
		panic(undefined{})
	}
	contents := fmt.Sprint(s.length)
	for i := int64(0); i < s.length; i++ {
		contents += fmt.Sprint(",", s.at(i))
	}
	if _, known := m.keys[contents]; !known {
		m.keys[contents] = int64(len(m.keys))
	}
	return m.keys[contents]
}

// table evaluates a sequence of sequences.
func (m model) table(t *logic.Term) func(index int64) seqValue {
	if t.Op == logic.OpConst {
		return m.maps[t.Name]
	}
	if t.Op == logic.OpIte {
		if m.eval(t.Args[0]) == 1 {
			return m.table(t.Args[1])
		}
		return m.table(t.Args[2])
	}
	if t.Op == logic.OpSpliceAt {
		base, ref, inside, lo, hi := m.table(t.Args[0]), m.eval(t.Args[1]), m.seq(t.Args[2]), m.eval(t.Args[3]), m.eval(t.Args[4])
		return func(index int64) seqValue {
			if index == ref {
				return spliced(base(index), inside, lo, hi)
			}
			return base(index)
		}
	}
	if t.Op == logic.OpWrite {
		base, ref, at, written := m.table(t.Args[0]), m.eval(t.Args[1]), m.eval(t.Args[2]), m.eval(t.Args[3])
		return func(index int64) seqValue {
			if index == ref {
				return base(index).with(at, written)
			}
			return base(index)
		}
	}
	if t.Op != logic.OpStore {
		panic("unexpected sequence of sequences " + t.String())
	}
	base, written, at := m.table(t.Args[0]), m.seq(t.Args[2]), m.eval(t.Args[1])
	return func(index int64) seqValue {
		if index == at {
			return written
		}
		return base(index)
	}
}

// eval computes the value of a ground term in a model. Booleans are 0 and 1.
// Division by zero has the value the model picks for it, and a term the model
// cannot evaluate panics with undefined.
func (m model) eval(t *logic.Term) int64 {
	arg := func(i int) int64 { return m.eval(t.Args[i]) }
	truth := func(b bool) int64 {
		if b {
			return 1
		}
		return 0
	}
	switch t.Op {
	case logic.OpIntLit:
		if t.Big != nil {
			panic(undefined{})
		}
		return t.Val
	case logic.OpTrue:
		return 1
	case logic.OpFalse:
		return 0
	case logic.OpConst, logic.OpBound:
		return m.ints[t.Name]
	case logic.OpAdd:
		return plus(arg(0), arg(1))
	case logic.OpMul:
		return times(arg(0), arg(1))
	case logic.OpNeg:
		return times(-1, arg(0))
	case logic.OpDiv, logic.OpMod:
		a, b, sign := arg(0), arg(1), int64(1)
		if t.Op == logic.OpMod {
			sign = -1
		}
		switch {
		case b == 0:
			// The logic says nothing about x/0 and x%0 beyond their being
			// functions of x, so a proof has to survive each of these.
			*m.divided = true
			switch m.wild {
			case 0:
				return 5 * sign
			case 1:
				return plus(a, sign)
			}
			return plus(times(-2, a), 3*sign)
		case b == -1 && t.Op == logic.OpDiv:
			return times(-1, a)
		case b == -1:
			return 0
		case t.Op == logic.OpDiv:
			return a / b
		}
		return a % b
	case logic.OpLen:
		return m.seq(t.Args[0]).length
	case logic.OpKey:
		return m.key(m.seq(t.Args[0]))
	case logic.OpSelect:
		return m.seq(t.Args[0]).at(arg(1))
	case logic.OpIsNil:
		return truth(arg(0) == 0)
	case logic.OpIs:
		return truth(m.is(arg(0), arg(1)))
	case logic.OpErrRef:
		// The reference at which the model reads what an error holds: a
		// function of the error that maps several errors to one
		// reference, as nothing says it is injective.
		return (arg(0)*arg(0) + m.relation) % 3
	case logic.OpPred:
		def := m.preds[t.Name]
		saved := make([]int64, len(t.Args))
		for i := range t.Args {
			saved[i] = arg(i)
		}
		// The parameters take the values of the arguments while the body
		// is evaluated, and get back the values an enclosing application
		// of the same predicate gave them.
		for i, param := range def.Params {
			saved[i], m.ints[param.Name] = m.ints[param.Name], saved[i]
		}
		result := m.eval(def.Body)
		for i, param := range def.Params {
			m.ints[param.Name] = saved[i]
		}
		return result
	case logic.OpIte:
		if arg(0) == 1 {
			return arg(1)
		}
		return arg(2)
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
		// Generated quantifiers with a guard range over [-2, 4], which
		// covers every index the generator can produce a bound for.
		name := t.Args[0].Name
		tried := []int64{-2, -1, 0, 1, 2, 3, 4}
		if strings.HasPrefix(name, "u#") {
			tried = append(tried, m.ints["x"], m.ints["y"], m.ints["z"])
		}
		for _, x := range tried {
			m.ints[name] = x
			if (arg(1) == 1) == (t.Op == logic.OpExists) {
				return truth(t.Op == logic.OpExists)
			}
		}
		// A quantifier over all integers is settled only by an instance:
		// one that fails a Forall or one that satisfies an Exists. Without
		// one the truth lies outside the values tried.
		if strings.HasPrefix(name, "u#") {
			panic(undefined{})
		}
		return truth(t.Op == logic.OpForall)
	}
	panic("unexpected term " + t.String())
}

func (m model) seq(t *logic.Term) seqValue {
	value := func(i int) int64 { return m.eval(t.Args[i]) }
	switch t.Op {
	case logic.OpConst:
		return m.seqs[t.Name]
	case logic.OpFill:
		filler := value(1)
		return seqValue{max(value(0), 0), func(int64) int64 { return filler }}
	case logic.OpSelect:
		return m.table(t.Args[0])(value(1))
	case logic.OpStore:
		return m.seq(t.Args[0]).with(value(1), value(2))
	case logic.OpPush:
		base := m.seq(t.Args[0])
		pushed := base.with(base.length, value(1))
		pushed.length = plus(base.length, 1)
		return pushed
	case logic.OpConcat:
		first, second := m.seq(t.Args[0]), m.seq(t.Args[1])
		return seqValue{plus(first.length, second.length), func(index int64) int64 {
			if index < first.length {
				return first.at(index)
			}
			return second.at(plus(index, times(-1, first.length)))
		}}
	case logic.OpIte:
		if value(0) == 1 {
			return m.seq(t.Args[1])
		}
		return m.seq(t.Args[2])
	case logic.OpSub:
		whole, lo := m.seq(t.Args[0]), value(1)
		return seqValue{max(plus(value(2), times(-1, lo)), 0), func(index int64) int64 { return whole.at(plus(lo, index)) }}
	case logic.OpSplice:
		return spliced(m.seq(t.Args[0]), m.seq(t.Args[1]), value(2), value(3))
	}
	panic("unexpected sequence " + t.String())
}

// generator builds random formulas over a few integers, one boolean, and one
// sequence. Quantifiers are bounded so that they can be evaluated exactly.
type generator struct {
	rng   *rand.Rand
	bound int
	vars  []*logic.Term
	// wide adds what the plain problems leave out: a second sequence,
	// filled sequences, numbers near the edge of 64 bits, predicates, errors
	// and the memory that holds them, conditional formulas, and quantifiers
	// over all integers. Bound variables are then named by how deeply they
	// are nested, so that quantifiers side by side share a name.
	wide   bool
	nested int
}

// extremes are the numbers a wide problem and its models draw on to reach
// the places where 64-bit arithmetic overflows.
var extremes = []int64{
	1 << 31, 1<<32 - 1, 1 << 32, 1<<32 + 1, 3037000500, 1 << 62, math.MaxInt64,
	-(1 << 31), -(1<<32 + 1), -(1 << 62), math.MinInt64, 1_000_000_007,
}

// definitions returns the predicates that wide problems apply: a plain
// property, a relation between two numbers, and a recursive one that holds
// of the powers of two.
func definitions() map[string]*logic.PredDef {
	n, lo, hi := logic.Bound("n", logic.Int), logic.Bound("lo", logic.Int), logic.Bound("hi", logic.Int)
	zero, one, two := logic.IntLit(0), logic.IntLit(1), logic.IntLit(2)
	halved := logic.And(logic.Lt(one, n), logic.Eq(logic.Mod(n, two), zero), logic.Pred("pow", logic.Div(n, two)))
	return map[string]*logic.PredDef{
		"pos":  {Name: "pos", Params: []*logic.Term{n}, Body: logic.Lt(zero, n)},
		"near": {Name: "near", Params: []*logic.Term{lo, hi}, Body: logic.And(logic.Le(lo, hi), logic.Le(hi, logic.Add(lo, two)))},
		"pow":  {Name: "pow", Params: []*logic.Term{n}, Body: logic.Or(logic.Eq(n, one), halved)},
	}
}

// failure builds an error: a named one, nil, one chosen by a condition, or
// one read from memory, possibly after a write.
func (g *generator) failure(depth int) *logic.Term {
	memory := logic.Const("E", logic.SeqOf(logic.Err))
	switch choice := g.rng.IntN(8); {
	case choice == 0:
		return logic.NilErr()
	case choice == 1:
		return logic.Select(memory, g.ref())
	case choice <= 3 && depth > 0:
		return logic.Ite(g.formula(depth-1), g.failure(depth-1), g.failure(depth-1))
	case choice <= 5 && depth > 0:
		return logic.Select(logic.Store(memory, g.ref(), g.failure(depth-1)), g.ref())
	}
	return logic.Const([]string{"e", "f"}[g.rng.IntN(2)], logic.Err)
}

// errorOverWrite says whether an error read from memory after a write is nil:
// as the written error is, or as the one that was there. Either is right only
// for the right relation between the two references, and the guard is
// sometimes missing or reversed.
func (g *generator) errorOverWrite() *logic.Term {
	memory := logic.Const("E", logic.SeqOf(logic.Err))
	at, read, written := g.ref(), g.ref(), g.failure(0)
	expected := []*logic.Term{written, logic.Select(memory, read)}[g.rng.IntN(2)]
	fact := logic.Iff(logic.IsNil(logic.Select(logic.Store(memory, at, written), read)), logic.IsNil(expected))
	switch g.rng.IntN(4) {
	case 0:
		return logic.Implies(logic.Eq(at, read), fact)
	case 1:
		return logic.Implies(logic.Ne(at, read), fact)
	}
	return fact
}

// ref picks a reference: one of two named ones, nil, or the reference at
// which what an error holds is read.
func (g *generator) ref() *logic.Term {
	if g.rng.IntN(5) == 0 {
		return logic.ErrRef(g.failure(0))
	}
	return []*logic.Term{logic.Const("r", logic.Ref), logic.Const("s", logic.Ref), logic.RefLit(0)}[g.rng.IntN(3)]
}

// table builds a sequence of sequences: a base, possibly with some of its
// sequences replaced, which is the shape memory has in the verifier.
func (g *generator) table(depth int) *logic.Term {
	// A choice between two memories is what joining the ends of a function
	// literal makes.
	if g.wide && depth > 0 && g.rng.IntN(4) == 0 {
		return logic.Ite(g.formula(depth-1), g.table(depth-1), g.table(depth-1))
	}
	if depth > 0 && g.rng.IntN(2) == 0 {
		return logic.Store(g.table(depth-1), g.intTerm(0), g.seq(depth-1))
	}
	// A write of one element of one sequence is how memory is written.
	if g.wide && depth > 0 && g.rng.IntN(2) == 0 {
		return logic.Write(g.table(depth-1), g.intTerm(0), g.intTerm(0), g.intTerm(0))
	}
	// A write of a stretch of unknown values is how a call writes what
	// an owner owns.
	if g.wide && depth > 0 && g.rng.IntN(3) == 0 {
		return logic.SpliceAt(g.table(depth-1), g.intTerm(0), g.seq(depth-1), g.intTerm(0), g.intTerm(0))
	}
	return logic.Const("M", logic.SeqOf(logic.IntSeq))
}

func (g *generator) seq(depth int) *logic.Term {
	base := logic.Const("A", logic.IntSeq)
	if g.wide && g.rng.IntN(3) == 0 {
		base = logic.Const("B", logic.IntSeq)
	}
	switch {
	case g.wide && g.rng.IntN(8) == 0:
		return logic.Fill(g.intTerm(0), g.intTerm(0))
	case g.wide && depth > 0 && g.rng.IntN(8) == 0:
		return logic.Ite(g.formula(depth-1), g.seq(depth-1), g.seq(depth-1))
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
	case g.wide && depth > 0 && g.rng.IntN(8) == 0:
		return logic.Splice(g.seq(depth-1), g.seq(depth-1), g.intTerm(0), g.intTerm(0))
	}
	return base
}

func (g *generator) intTerm(depth int) *logic.Term {
	if depth <= 0 || g.rng.IntN(3) == 0 {
		if g.wide && g.rng.IntN(10) == 0 {
			return logic.IntLit(extremes[g.rng.IntN(len(extremes))])
		}
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
		if g.wide {
			switch g.rng.IntN(13) {
			case 12:
				return g.splicedLaw()
			case 0:
				return logic.Pred("pos", g.intTerm(depth))
			case 1:
				return logic.Pred("near", g.intTerm(0), g.intTerm(0))
			case 2:
				return logic.Pred("pow", g.intTerm(0))
			case 3, 4:
				return logic.IsNil(g.failure(depth))
			case 5:
				return logic.Eq(g.ref(), g.ref())
			case 6:
				return g.errorOverWrite()
			case 7:
				// A quantifier side by side with others of the same name.
				u := logic.Bound(fmt.Sprintf("u#%d", g.nested), logic.Int)
				found := []*logic.Term{logic.Eq(u, g.intTerm(0)), logic.Lt(u, g.intTerm(0)), logic.Lt(g.intTerm(0), u)}[g.rng.IntN(3)]
				if g.rng.IntN(3) == 0 {
					found = logic.Eq(logic.Select(g.seq(0), u), g.intTerm(0))
				}
				return logic.Exists(u, found)
			case 8:
				// A division of two numbers, with a claim about the
				// result that is right about one time in three.
				a, b := int64(g.rng.IntN(19)-9), int64(g.rng.IntN(9)-4)
				claimed := int64(g.rng.IntN(7) - 3)
				if b != 0 && g.rng.IntN(3) == 0 {
					claimed = []int64{a / b, a % b}[g.rng.IntN(2)]
				}
				if g.rng.IntN(2) == 0 {
					return logic.Eq(logic.Div(logic.IntLit(a), logic.IntLit(b)), logic.IntLit(claimed))
				}
				return logic.Eq(logic.Mod(logic.IntLit(a), logic.IntLit(b)), logic.IntLit(claimed))
			case 9:
				return logic.Eq(g.failure(depth), g.failure(depth))
			case 10:
				return logic.Is(g.failure(depth), g.failure(depth))
			case 11:
				// Two errors are the same, or one of them is nil: false of
				// two different errors, which a translation that compared
				// errors only by whether they are nil would miss.
				a, b := g.failure(0), g.failure(0)
				return logic.Or(logic.Eq(a, b), logic.IsNil(a), logic.IsNil(b))
			}
		}
		a, b := g.intTerm(depth), g.intTerm(depth)
		switch g.rng.IntN(14) {
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
		case 11:
			return g.keyed()
		}
		return logic.Const("p", logic.Bool)
	}
	if g.wide && g.rng.IntN(8) == 0 {
		return logic.Ite(g.formula(depth-1), g.formula(depth-1), g.formula(depth-1))
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
	// A wide problem sometimes drops the guard, which leaves a quantifier
	// over all integers; the name tells the model which kind it is.
	unguarded := g.wide && g.rng.IntN(3) == 0
	if g.wide {
		x = logic.Bound(fmt.Sprintf("x#%d", g.nested), logic.Int)
	}
	if unguarded {
		x = logic.Bound(fmt.Sprintf("u#%d", g.nested), logic.Int)
	}
	saved := g.vars
	g.vars = append(append([]*logic.Term(nil), g.vars...), x)
	// The upper bound never exceeds 4 in any generated model.
	lo, hi := logic.IntLit(int64(g.rng.IntN(3)-1)), logic.IntLit(int64(g.rng.IntN(4)))
	if g.rng.IntN(2) == 0 {
		hi = logic.Len(logic.Const("A", logic.IntSeq))
	}
	if g.wide && g.rng.IntN(4) == 0 {
		hi = logic.Len(logic.Const("B", logic.IntSeq))
	}
	g.nested++
	body := g.formula(depth - 1)
	g.nested--
	g.vars = saved
	if unguarded {
		if g.rng.IntN(2) == 0 {
			return logic.Forall(x, body)
		}
		return logic.Exists(x, body)
	}
	guard := logic.And(logic.Le(lo, x), logic.Lt(x, hi))
	if g.rng.IntN(2) == 0 {
		return logic.Forall(x, logic.Implies(guard, body))
	}
	return logic.Exists(x, logic.And(guard, body))
}

// splicedLaw states a fact about a read or the length of a splice, of a
// sequence or of a table's sequence. About half of the generated facts are
// the true law and the rest read past an end of the stretch, read the
// wrong sequence, or are off by one.
func (g *generator) splicedLaw() *logic.Term {
	whole, inside := g.seq(1), g.seq(1)
	j, lo, hi := g.intTerm(0), g.intTerm(0), g.intTerm(0)
	slack := logic.IntLit(int64(g.rng.IntN(3) / 2))
	result := logic.Splice(whole, inside, lo, hi)
	if g.rng.IntN(2) == 0 {
		// The same through a table, read at its row or at another.
		table, ref, other := g.table(1), g.intTerm(0), g.intTerm(0)
		whole = logic.Select(table, ref)
		spliced := logic.SpliceAt(table, ref, inside, lo, hi)
		if g.rng.IntN(3) == 0 {
			return logic.Implies(logic.Ne(other, ref), logic.Eq(logic.Select(logic.Select(spliced, other), j), logic.Select(logic.Select(table, other), logic.Add(j, slack))))
		}
		result = logic.Select(spliced, ref)
	}
	within := logic.And(logic.Le(lo, j), logic.Lt(j, hi))
	read := logic.Select(result, j)
	switch g.rng.IntN(6) {
	case 0:
		return logic.Implies(within, logic.Eq(read, logic.Select(inside, logic.Add(j, slack))))
	case 1:
		return logic.Implies(logic.Not(within), logic.Eq(read, logic.Select(whole, logic.Add(j, slack))))
	case 2:
		return logic.Eq(logic.Len(result), logic.Add(logic.Len([]*logic.Term{whole, inside}[g.rng.IntN(2)]), slack))
	case 3:
		// Reads at the ends of the stretch.
		at := []*logic.Term{lo, hi, logic.Sub(hi, logic.IntLit(1))}[g.rng.IntN(3)]
		half := []*logic.Term{whole, inside}[g.rng.IntN(2)]
		return logic.Implies(logic.Lt(lo, hi), logic.Eq(logic.Select(result, at), logic.Select(half, at)))
	case 4:
		return logic.Eq(read, logic.Select([]*logic.Term{whole, inside}[g.rng.IntN(2)], j))
	}
	return logic.Implies(logic.Le(hi, lo), logic.Eq(read, logic.Select(whole, logic.Add(j, slack))))
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

// keyed states a fact about the keys of two short sequences: that they are
// equal, or what follows if they are. Equal keys mean equal lengths and equal
// elements inside the length, and nothing about elements outside it.
func (g *generator) keyed() *logic.Term {
	short := func() *logic.Term {
		base := logic.Const("A", logic.IntSeq)
		if g.wide && g.rng.IntN(2) == 0 {
			base = logic.Const("B", logic.IntSeq)
		}
		switch g.rng.IntN(4) {
		case 0:
			return logic.Store(base, g.intTerm(0), g.intTerm(0))
		case 1:
			return logic.Push(base, g.intTerm(0))
		case 2:
			return logic.Subseq(base, logic.IntLit(int64(g.rng.IntN(2))), logic.IntLit(int64(g.rng.IntN(4))))
		}
		return base
	}
	s, t, j := short(), short(), g.intTerm(0)
	same := logic.Eq(logic.Key(s), logic.Key(t))
	switch g.rng.IntN(5) {
	case 0:
		return same
	case 1:
		return logic.Implies(same, logic.Eq(logic.Len(s), logic.Len(t)))
	case 2:
		return logic.Implies(same, logic.Eq(logic.Select(s, j), logic.Select(t, j)))
	case 3:
		inside := logic.And(logic.Le(logic.IntLit(0), j), logic.Lt(j, logic.Len(s)))
		return logic.Implies(logic.And(same, inside), logic.Eq(logic.Select(s, j), logic.Select(t, j)))
	}
	return logic.Implies(logic.Eq(logic.Len(s), logic.Len(t)), same)
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

// models returns the models that proved goals are checked against. The small
// ones take every combination of a few values for the integers and a few
// shapes for the sequences. The large ones are drawn at random and put some
// of the integers near the edge of 64 bits. Everything a plain problem never
// mentions is drawn at random in both.
func models() (small, large []model) {
	rng := rand.New(rand.NewPCG(5, 6))
	build := func(x, y, z, shape int64) model {
		second, errs := int64(rng.IntN(12)), int64(rng.IntN(3))
		return model{
			ints: map[string]int64{
				"x": x, "y": y, "z": z, "p": shape % 2,
				"e": int64(rng.IntN(3)), "f": int64(rng.IntN(3)), "r": int64(rng.IntN(3)), "s": int64(rng.IntN(3)),
			},
			seqs: map[string]seqValue{
				"A": {shape % 4, func(i int64) int64 { return (shape%3 + i*i) % 3 }},
				"B": {second % 4, func(i int64) int64 { return (second/4 + i*i*(second%2+1)) % 3 }},
				// The errors in memory, of which those numbered zero are nil.
				"E": {3, func(i int64) int64 { return (errs + i*i) % 3 }},
			},
			keys: map[string]int64{},
			maps: map[string]func(int64) seqValue{"M": func(r int64) seqValue {
				// Rows differ in length and content, and some
				// rows coincide.
				row := (r*r + shape) % 3
				return seqValue{(row + shape/4) % 3, func(i int64) int64 { return (row*i + shape/6) % 3 }}
			}},
			preds:    definitions(),
			relation: int64(rng.IntN(3)),
		}
	}
	for x := int64(-2); x <= 2; x++ {
		for y := int64(-2); y <= 2; y++ {
			for z := int64(-1); z <= 1; z++ {
				for shape := int64(0); shape < 12; shape++ {
					small = append(small, build(x, y, z, shape))
				}
			}
		}
	}
	for range 600 {
		var values [3]int64
		for i := range values {
			values[i] = int64(rng.IntN(7) - 3)
			if rng.IntN(2) == 0 {
				// An extreme itself, or a number right next to one.
				values[i] = extremes[rng.IntN(len(extremes))]
				if values[i] > math.MinInt64+1 && values[i] < math.MaxInt64-1 {
					values[i] += int64(rng.IntN(3) - 1)
				}
			}
		}
		large = append(large, build(values[0], values[1], values[2], int64(rng.IntN(12))))
	}
	return small, large
}

// counterexample searches the given models for one that satisfies every
// hypothesis and falsifies the goal. A model in which something divides by
// zero is tried once for each meaning it can give to such a division.
func counterexample(hyps []*logic.Term, goal *logic.Term, models []model) (found bool, description string) {
	holds := func(m model, t *logic.Term) (result, defined bool) {
		defer func() {
			if r := recover(); r != nil {
				if _, ok := r.(undefined); !ok {
					panic(r)
				}
				defined = false
			}
		}()
		return m.eval(t) == 1, true
	}
	for _, m := range models {
		divided := true
		m.divided = &divided
		for m.wild = 0; m.wild < 3 && divided; m.wild++ {
			divided = false
			clear(m.keys)
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
				return true, fmt.Sprintf("%v, division by zero number %d", m.ints, m.wild)
			}
		}
	}
	return false, ""
}

// TestProveIsSound checks the one property the translation and Z3 together
// must never violate: a proved goal holds in every model of the
// hypotheses. Random problems are
// proved and then evaluated over many models. The plain problems are about
// integers, one boolean, and the sequences built from one; the wide ones add
// every other kind of term the logic has.
func TestProveIsSound(t *testing.T) {
	// VEGO_CACHE names a cache of answers that this test may use; every
	// proved goal is still checked by evaluation, so a wrong answer kept
	// there is caught as a wrong answer of Z3 is. Without it, Z3 answers.
	z3, err := Open("", os.Getenv("VEGO_CACHE"))
	if err != nil {
		t.Fatal(err)
	}
	small, large := models()
	tests := []struct {
		name     string
		wide     bool
		seed     uint64
		problems int
		least    int
		models   []model
		// without solves every problem without the axiom of
		// extensionality, as the encoder chooses for some problems; see
		// tacticWithoutExtensionality. The problems are those of the test
		// with the same seed solved with it.
		without bool
		// noEMatching solves every problem without e-matching, as the
		// first attempt at a contradiction check does; see Model.
		noEMatching bool
	}{
		{"plain problems", false, 1, 4000, 1000, small, false, false},
		{"wide problems", true, 3, 4000, 1100, append(small, large...), false, false},
		{"plain problems without extensionality", false, 1, 4000, 1000, small, true, false},
		{"wide problems without extensionality", true, 3, 4000, 1100, append(small, large...), true, false},
		{"wide problems without e-matching", true, 3, 4000, 1100, append(small, large...), false, true},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			rng := rand.New(rand.NewPCG(test.seed, test.seed+1))
			type problem struct {
				hyps []*logic.Term
				goal *logic.Term
			}
			problems := make([]problem, test.problems)
			for i := range problems {
				g := &generator{rng: rng, wide: test.wide, vars: []*logic.Term{
					logic.Const("x", logic.Int), logic.Const("y", logic.Int), logic.Const("z", logic.Int),
				}}
				var hyps []*logic.Term
				for range rng.IntN(4) {
					hyps = append(hyps, g.formula(2))
				}
				problems[i] = problem{hyps, g.formula(2 + rng.IntN(2))}
			}
			// The problems are solved by as many workers as the solver
			// keeps processes, and checked in order.
			results := make([]Result, len(problems))
			var wg sync.WaitGroup
			next := make(chan int)
			for range maxProcesses {
				wg.Go(func() {
					for i := range next {
						results[i] = z3.Prove(problems[i].hyps, problems[i].goal, Options{Preds: definitions(), Effort: 200_000, withoutExtensionality: test.without, withoutEMatching: test.noEMatching})
					}
				})
			}
			for i := range problems {
				next <- i
			}
			close(next)
			wg.Wait()
			proved := 0
			for i, p := range problems {
				if results[i] != Proved {
					continue
				}
				proved++
				if found, m := counterexample(p.hyps, p.goal, test.models); found {
					t.Fatalf("problem %d: proved a goal that fails\nhyps: %v\ngoal: %v\nmodel: %v", i, p.hyps, p.goal, m)
				}
			}
			if proved < test.least {
				t.Fatalf("only %d random problems were proved; the test has lost its power", proved)
			}
			t.Logf("proved %d random problems, all confirmed by evaluation over %d models", proved, len(test.models))
		})
	}
}

// TestExtremeCoefficients checks goals that are false and whose numbers lie
// at the edge of the 64-bit range: a literal written with the wrong sign or
// cut to 64 bits on its way to Z3 would make some of them provable.
func TestExtremeCoefficients(t *testing.T) {
	z3 := solverFor(t)
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
			if z3.Prove([]*logic.Term{test.hyp}, logic.Le(x, zero), Options{}) == Proved {
				t.Fatalf("proved x <= 0 from %v, which x = 1 satisfies", test.hyp)
			}
		})
	}
}

// TestNilThroughMemory checks that whether an error read from memory is nil
// follows the write it was read after: the same reference sees the written
// error, and another reference sees what was there before.
func TestNilThroughMemory(t *testing.T) {
	z3 := solverFor(t)
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
		{"unknown reference may see either", []*logic.Term{logic.Not(logic.IsNil(logic.Select(memory, q)))}, read, Refuted},
		{"unknown reference may see the old error", []*logic.Term{logic.Not(logic.IsNil(logic.Select(memory, q)))}, logic.Not(read), Refuted},
		{
			"a written error that is not nil is not nil when read back",
			[]*logic.Term{logic.Not(logic.IsNil(failed))},
			logic.Not(logic.IsNil(logic.Select(logic.Store(memory, p, failed), p))), Proved,
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got := z3.Prove(test.hyps, test.goal, Options{})

			if got != test.want {
				t.Fatalf("Prove(%v, %v) = %v, want %v", test.hyps, test.goal, got, test.want)
			}
		})
	}
}

// TestRules checks the meaning of single operators of the logic on problems
// small enough to decide by hand. Each problem is one that a particular
// wrong translation gets wrong, and the random problems of TestProveIsSound
// reach too rarely to be relied on for it.
func TestRules(t *testing.T) {
	z3 := solverFor(t)
	x, y, z := logic.Const("x", logic.Int), logic.Const("y", logic.Int), logic.Const("z", logic.Int)
	c := logic.Const("c", logic.Bool)
	e, f := logic.Const("e", logic.Err), logic.Const("f", logic.Err)
	lit := logic.IntLit
	atMost := func(v *logic.Term) *logic.Term { return logic.Le(v, lit(0)) }
	n := logic.Bound("n", logic.Int)
	pos := Options{Preds: map[string]*logic.PredDef{"pos": {Name: "pos", Params: []*logic.Term{n}, Body: logic.Lt(lit(0), n)}}}
	bound := logic.Bound("w", logic.Int)
	chosen := logic.Ite(c, e, f)
	seqA, seqB := logic.Const("A", logic.IntSeq), logic.Const("B", logic.IntSeq)
	tableM, tableN := logic.Const("M", logic.SeqOf(logic.IntSeq)), logic.Const("N", logic.SeqOf(logic.IntSeq))
	keyVar, keys := logic.Bound("s", logic.IntSeq), logic.Const("H", logic.BoolSeq)
	marks, otherKey := logic.Const("G", logic.BoolSeq), logic.Bound("t", logic.IntSeq)
	keptButA := logic.Forall(otherKey, logic.Implies(logic.And(logic.Select(keys, logic.Key(otherKey)), logic.Ne(logic.Key(otherKey), logic.Key(seqA))),
		logic.Select(marks, logic.Key(otherKey))))
	tiedToA := logic.Iff(logic.Eq(logic.Key(keyVar), logic.Key(seqA)), logic.SeqEq(keyVar, seqA, logic.Bound("i", logic.Int)))
	tests := []struct {
		name string
		opts Options
		hyps []*logic.Term
		goal *logic.Term
		want Result
	}{
		// Guards against a filled sequence of the wrong length.
		{"the length of a filled sequence", Options{}, []*logic.Term{logic.Le(lit(0), x)}, logic.Eq(logic.Len(logic.Fill(x, y)), x), Proved},
		// Guards against a sequence built with a negative length keeping
		// that length, and against a named sequence having one.
		{"a sequence built with a negative length is empty", Options{}, []*logic.Term{logic.Lt(x, lit(0))}, logic.Eq(logic.Len(logic.Fill(x, y)), lit(0)), Proved},
		{"a sequence built with a negative length has no other length", Options{}, []*logic.Term{logic.Lt(x, lit(0))}, logic.Eq(logic.Len(logic.Fill(x, y)), x), Refuted},
		{"a cut with its ends reversed is empty", Options{}, []*logic.Term{logic.Lt(y, x)}, logic.Eq(logic.Len(logic.Subseq(logic.Const("A", logic.IntSeq), x, y)), lit(0)), Proved},
		{"a named sequence has no negative length", Options{}, nil, logic.Le(lit(0), logic.Len(logic.Const("A", logic.IntSeq))), Proved},
		{"a sequence held in another has no negative length", Options{}, nil, logic.Le(lit(0), logic.Len(logic.Select(logic.Const("M", logic.SeqOf(logic.IntSeq)), x))), Proved},
		{"a filled sequence is not empty", Options{}, nil, logic.Eq(logic.Len(logic.Fill(lit(3), y)), lit(0)), Refuted},
		// Guards against a filled sequence holding something other than
		// the value it was filled with.
		{"an element of a filled sequence", Options{}, nil, logic.Eq(logic.Select(logic.Fill(x, y), z), y), Proved},
		{"a filled sequence does not hold zero", Options{}, nil, logic.Eq(logic.Select(logic.Fill(x, y), z), lit(0)), Refuted},
		// Guards against a splice reading the wrong sequence, or either
		// end of its stretch on the wrong side, and against a spliced
		// table reaching another row or another table.
		{"a splice holds the inside in its stretch", Options{}, []*logic.Term{logic.Le(x, z), logic.Lt(z, y)}, logic.Eq(logic.Select(logic.Splice(seqA, seqB, x, y), z), logic.Select(seqB, z)), Proved},
		{"a splice holds the inside at the start of its stretch", Options{}, []*logic.Term{logic.Lt(x, y)}, logic.Eq(logic.Select(logic.Splice(seqA, seqB, x, y), x), logic.Select(seqB, x)), Proved},
		{"a splice keeps the sequence at the end of its stretch", Options{}, nil, logic.Eq(logic.Select(logic.Splice(seqA, seqB, x, y), y), logic.Select(seqA, y)), Proved},
		{"a splice does not hold the inside at the end of its stretch", Options{}, nil, logic.Eq(logic.Select(logic.Splice(seqA, seqB, x, y), y), logic.Select(seqB, y)), Refuted},
		{"a splice keeps the sequence before its stretch", Options{}, []*logic.Term{logic.Lt(z, x)}, logic.Eq(logic.Select(logic.Splice(seqA, seqB, x, y), z), logic.Select(seqA, z)), Proved},
		{"a splice does not keep the sequence in its stretch", Options{}, []*logic.Term{logic.Le(x, z), logic.Lt(z, y)}, logic.Eq(logic.Select(logic.Splice(seqA, seqB, x, y), z), logic.Select(seqA, z)), Refuted},
		{"a splice is as long as the sequence", Options{}, nil, logic.Eq(logic.Len(logic.Splice(seqA, seqB, x, y)), logic.Len(seqA)), Proved},
		{"a splice is not as long as the inside", Options{}, nil, logic.Eq(logic.Len(logic.Splice(seqA, seqB, x, y)), logic.Len(seqB)), Refuted},
		// The same of a splice that Z3 sees whole, as under a write, where
		// its definition is what Z3 reads rather than the reads the
		// encoder reduces.
		{"a written splice holds the inside in its stretch", Options{}, []*logic.Term{logic.Le(x, z), logic.Lt(z, y), logic.Lt(z, lit(10))}, logic.Eq(logic.Select(logic.Store(logic.Splice(seqA, seqB, x, y), lit(10), lit(0)), z), logic.Select(seqB, z)), Proved},
		{"a written splice keeps the sequence at the end of its stretch", Options{}, []*logic.Term{logic.Lt(y, lit(10))}, logic.Eq(logic.Select(logic.Store(logic.Splice(seqA, seqB, x, y), lit(10), lit(0)), y), logic.Select(seqA, y)), Proved},
		{"a written splice keeps the sequence before its stretch", Options{}, []*logic.Term{logic.Lt(z, x), logic.Lt(z, lit(10))}, logic.Eq(logic.Select(logic.Store(logic.Splice(seqA, seqB, x, y), lit(10), lit(0)), z), logic.Select(seqA, z)), Proved},
		{"a written splice is as long as the sequence", Options{}, nil, logic.Eq(logic.Len(logic.Store(logic.Splice(seqA, seqB, x, y), lit(10), lit(0))), logic.Len(seqA)), Proved},
		{"a written row of a spliced table holds the inside in its stretch", Options{}, []*logic.Term{logic.Le(y, lit(0)), logic.Lt(lit(0), z)}, logic.Eq(logic.Select(logic.Store(logic.Select(logic.SpliceAt(tableM, x, seqA, y, z), x), lit(10), lit(0)), lit(0)), logic.Select(seqA, lit(0))), Proved},
		{"a written row of a spliced table keeps its other rows", Options{}, []*logic.Term{logic.Ne(x, y)}, logic.Eq(logic.Select(logic.Store(logic.Select(logic.SpliceAt(tableM, x, seqA, lit(0), z), y), lit(10), lit(0)), lit(0)), logic.Select(logic.Select(tableM, y), lit(0))), Proved},
		{"a written row of a spliced table keeps the row at the end of the stretch", Options{}, []*logic.Term{logic.Le(lit(0), z)}, logic.Eq(logic.Select(logic.Store(logic.Select(logic.SpliceAt(tableM, x, seqA, lit(0), z), x), lit(-1), lit(0)), z), logic.Select(logic.Select(tableM, x), z)), Proved},
		{"a spliced table holds the inside at its row", Options{}, []*logic.Term{logic.Le(y, lit(0)), logic.Lt(lit(0), z)}, logic.Eq(logic.Select(logic.Select(logic.SpliceAt(tableM, x, seqA, y, z), x), lit(0)), logic.Select(seqA, lit(0))), Proved},
		{"a spliced table keeps its row outside the stretch", Options{}, []*logic.Term{logic.Lt(lit(0), y)}, logic.Eq(logic.Select(logic.Select(logic.SpliceAt(tableM, x, seqA, y, z), x), lit(0)), logic.Select(logic.Select(tableM, x), lit(0))), Proved},
		{"a spliced table keeps its other rows", Options{}, []*logic.Term{logic.Ne(x, y)}, logic.Eq(logic.Select(logic.Select(logic.SpliceAt(tableM, x, seqA, lit(0), z), y), lit(0)), logic.Select(logic.Select(tableM, y), lit(0))), Proved},
		{"a spliced table does not keep its row in the stretch", Options{}, []*logic.Term{logic.Le(y, lit(0)), logic.Lt(lit(0), z)}, logic.Eq(logic.Select(logic.Select(logic.SpliceAt(tableM, x, seqA, y, z), x), lit(0)), logic.Select(logic.Select(tableM, x), lit(0))), Refuted},
		{"a spliced table does not hold the inside at its other rows", Options{}, []*logic.Term{logic.Ne(x, y), logic.Lt(lit(0), z)}, logic.Eq(logic.Select(logic.Select(logic.SpliceAt(tableM, x, seqA, lit(0), z), y), lit(0)), logic.Select(seqA, lit(0))), Refuted},
		// Guards against a predicate known to be false being unfolded as
		// if it were true.
		{"a false predicate denies its body", pos, []*logic.Term{logic.Not(logic.Pred("pos", x))}, atMost(x), Proved},
		{"a false predicate does not give its body", pos, []*logic.Term{logic.Not(logic.Pred("pos", x))}, logic.Lt(lit(0), x), Refuted},
		{"a true predicate gives its body", pos, []*logic.Term{logic.Pred("pos", x)}, logic.Lt(lit(0), x), Proved},
		// Guards against the branches of a conditional error being
		// swapped when asking whether it is nil.
		{"a chosen error is the first when the condition holds", Options{}, []*logic.Term{c, logic.IsNil(e), logic.Not(logic.IsNil(f))}, logic.IsNil(chosen), Proved},
		{"a chosen error is not the second when the condition holds", Options{}, []*logic.Term{c, logic.IsNil(e), logic.Not(logic.IsNil(f))}, logic.Not(logic.IsNil(chosen)), Refuted},
		{"a chosen error is the second when the condition fails", Options{}, []*logic.Term{logic.Not(c), logic.IsNil(e), logic.Not(logic.IsNil(f))}, logic.Not(logic.IsNil(chosen)), Proved},
		// Guards against the branches of a conditional formula being
		// swapped.
		{"a conditional formula gives its first branch", Options{}, []*logic.Term{c, logic.Ite(c, atMost(x), logic.Lt(lit(0), x))}, atMost(x), Proved},
		{"a conditional formula does not give its second branch", Options{}, []*logic.Term{c, logic.Ite(c, atMost(x), logic.Lt(lit(0), x))}, logic.Lt(lit(0), x), Refuted},
		{"a refuted conditional formula refutes its first branch", Options{}, []*logic.Term{c, logic.Not(logic.Ite(c, atMost(x), atMost(y)))}, logic.Lt(lit(0), x), Proved},
		{"a refuted conditional formula leaves its second branch", Options{}, []*logic.Term{c, logic.Not(logic.Ite(c, atMost(x), atMost(y)))}, logic.Lt(lit(0), y), Refuted},
		// Guards against the branches of a conditional sequence, or of a
		// conditional sequence of sequences, being swapped. Joining the ends
		// of a function literal makes both: a string or slice that differs
		// between the ends, and a region of memory.
		{"a chosen sequence is the first when the condition holds", Options{}, []*logic.Term{c, logic.Eq(logic.Select(seqA, lit(0)), lit(1)), logic.Eq(logic.Select(seqB, lit(0)), lit(2))}, logic.Eq(logic.Select(logic.Ite(c, seqA, seqB), lit(0)), lit(1)), Proved},
		{"a chosen sequence is not the second when the condition holds", Options{}, []*logic.Term{c, logic.Eq(logic.Select(seqA, lit(0)), lit(1)), logic.Eq(logic.Select(seqB, lit(0)), lit(2))}, logic.Eq(logic.Select(logic.Ite(c, seqA, seqB), lit(0)), lit(2)), Refuted},
		{"a chosen sequence is the second when the condition fails", Options{}, []*logic.Term{logic.Not(c), logic.Eq(logic.Len(seqA), lit(1)), logic.Eq(logic.Len(seqB), lit(2))}, logic.Eq(logic.Len(logic.Ite(c, seqA, seqB)), lit(2)), Proved},
		{"a chosen table is the first when the condition holds", Options{}, []*logic.Term{c, logic.Eq(logic.Select(logic.Select(tableM, x), lit(0)), lit(1)), logic.Eq(logic.Select(logic.Select(tableN, x), lit(0)), lit(2))}, logic.Eq(logic.Select(logic.Select(logic.Ite(c, tableM, tableN), x), lit(0)), lit(1)), Proved},
		{"a chosen table is not the second when the condition holds", Options{}, []*logic.Term{c, logic.Eq(logic.Select(logic.Select(tableM, x), lit(0)), lit(1)), logic.Eq(logic.Select(logic.Select(tableN, x), lit(0)), lit(2))}, logic.Eq(logic.Select(logic.Select(logic.Ite(c, tableM, tableN), x), lit(0)), lit(2)), Refuted},
		{"a chosen table is the second when the condition fails", Options{}, []*logic.Term{logic.Not(c), logic.Eq(logic.Select(logic.Select(tableM, x), lit(0)), lit(1)), logic.Eq(logic.Select(logic.Select(tableN, x), lit(0)), lit(2))}, logic.Eq(logic.Select(logic.Select(logic.Ite(c, tableM, tableN), x), lit(0)), lit(2)), Proved},
		// Guards against a write of one element of one sequence of a table
		// reaching the wrong sequence or the wrong element, or losing the
		// rest of the sequence it writes.
		{"a written element is read back", Options{}, nil, logic.Eq(logic.Select(logic.Select(logic.Write(tableM, x, y, z), x), y), z), Proved},
		{"a write leaves the other elements of its sequence", Options{}, []*logic.Term{logic.Ne(y, z)}, logic.Eq(logic.Select(logic.Select(logic.Write(tableM, x, y, lit(5)), x), z), logic.Select(logic.Select(tableM, x), z)), Proved},
		{"a write leaves the other sequences", Options{}, []*logic.Term{logic.Ne(x, y)}, logic.Eq(logic.Select(logic.Select(logic.Write(tableM, x, z, lit(5)), y), z), logic.Select(logic.Select(tableM, y), z)), Proved},
		{"a write does not reach another sequence", Options{}, []*logic.Term{logic.Ne(x, y)}, logic.Eq(logic.Select(logic.Select(logic.Write(tableM, x, z, lit(5)), y), z), lit(5)), Refuted},
		{"a write keeps the length of its sequence", Options{}, nil, logic.Eq(logic.Len(logic.Select(logic.Write(tableM, x, y, z), x)), logic.Len(logic.Select(tableM, x))), Proved},
		// Guards against a quantifier over the keys of a map with string
		// keys, whose variable is a sequence, being lost or misread: it is
		// instantiated at a string whose key the map has, says nothing of
		// one whose key it may lack, and its key function tells nothing
		// apart inside the quantifier, which only keeps facts from being
		// proved.
		{"a fact of every string key holds of one the map has", Options{}, []*logic.Term{
			logic.Forall(keyVar, logic.Implies(logic.Select(keys, logic.Key(keyVar)), logic.Le(logic.Len(keyVar), lit(3)))),
			logic.Select(keys, logic.Key(seqA))}, logic.Le(logic.Len(seqA), lit(3)), Proved},
		// Z3 builds no model of a fact over every sequence, so what is
		// not proved here is unknown, not refuted.
		{"a fact of every string key says no more than it says", Options{}, []*logic.Term{
			logic.Forall(keyVar, logic.Implies(logic.Select(keys, logic.Key(keyVar)), logic.Le(logic.Len(keyVar), lit(3)))),
			logic.Select(keys, logic.Key(seqA))}, logic.Le(logic.Len(seqA), lit(2)), Unknown},
		{"a fact of every string key says nothing of one the map may lack", Options{}, []*logic.Term{
			logic.Forall(keyVar, logic.Implies(logic.Select(keys, logic.Key(keyVar)), logic.Le(logic.Len(keyVar), lit(3))))},
			logic.Le(logic.Len(seqA), lit(3)), Refuted},
		{"some string key the map has is found", Options{}, []*logic.Term{
			logic.Select(keys, logic.Key(seqA)), logic.Eq(logic.Len(seqA), lit(2))},
			logic.Exists(keyVar, logic.And(logic.Select(keys, logic.Key(keyVar)), logic.Eq(logic.Len(keyVar), lit(2)))), Proved},
		{"no string key is found in a map that has none", Options{}, []*logic.Term{
			logic.Forall(keyVar, logic.Not(logic.Select(keys, logic.Key(keyVar))))},
			logic.Exists(keyVar, logic.Select(keys, logic.Key(keyVar))), Refuted},
		// Guards against the tie of a bound string key to a string it is
		// compared with, which a quantifier over string keys carries in its
		// guard, being lost. What a write keeps is said of key numbers,
		// every key but that of A; a contract says it of strings, every key
		// but A, with the tie in its guard. With the tie the one follows
		// from the other; without it a key that is not A could have the
		// number of A.
		{"a key that is not a string has another number, by the tie of the guard", Options{}, []*logic.Term{keptButA},
			logic.Forall(keyVar, logic.Implies(logic.And(logic.Select(keys, logic.Key(keyVar)), tiedToA),
				logic.Or(logic.SeqEq(keyVar, seqA, logic.Bound("j", logic.Int)), logic.Select(marks, logic.Key(keyVar))))), Proved},
		{"without the tie a key that is not a string may have its number", Options{}, []*logic.Term{keptButA},
			logic.Forall(keyVar, logic.Implies(logic.Select(keys, logic.Key(keyVar)),
				logic.Or(logic.SeqEq(keyVar, seqA, logic.Bound("j", logic.Int)), logic.Select(marks, logic.Key(keyVar))))), Refuted},
		{"the tie says nothing of the key it excepts", Options{}, []*logic.Term{keptButA},
			logic.Forall(keyVar, logic.Implies(logic.And(logic.Select(keys, logic.Key(keyVar)), tiedToA), logic.Select(marks, logic.Key(keyVar)))), Refuted},
		// Guards against the remainder of two numbers being computed the
		// Euclidean way, which never yields a negative remainder, and the
		// quotient being rounded down. Go truncates: -7 / 2 is -3 and
		// -7 % 2 is -1.
		{"a remainder takes the sign of the dividend", Options{}, nil, logic.Eq(logic.Mod(lit(-7), lit(2)), lit(-1)), Proved},
		{"a remainder is not Euclidean", Options{}, nil, logic.Eq(logic.Mod(lit(-7), lit(2)), lit(1)), Refuted},
		{"a remainder by a negative number", Options{}, nil, logic.Eq(logic.Mod(lit(-7), lit(-2)), lit(-1)), Proved},
		{"a quotient truncates toward zero", Options{}, nil, logic.Eq(logic.Div(lit(-7), lit(2)), lit(-3)), Proved},
		{"a quotient is not rounded down", Options{}, nil, logic.Eq(logic.Div(lit(-7), lit(2)), lit(-4)), Refuted},
		// Guards against the law x = y*(x/y) + x%y being assumed when y is
		// zero, where it would make x%0 equal to x. Nothing is known about
		// a division by zero.
		{"a remainder by zero is not the dividend", Options{}, nil, logic.Eq(logic.Mod(x, lit(0)), x), Refuted},
		{"a remainder by an unknown that is zero", Options{}, []*logic.Term{logic.Eq(y, lit(0))}, logic.Eq(logic.Mod(x, y), x), Refuted},
		{"a quotient by an unknown that is zero", Options{}, []*logic.Term{logic.Eq(y, lit(0)), logic.Eq(logic.Div(x, y), lit(1))}, logic.Eq(logic.Mod(x, y), x), Refuted},
		{"the law of division holds for other divisors", Options{}, []*logic.Term{logic.Ne(y, lit(0))}, logic.Eq(logic.Add(logic.Mul(y, logic.Div(x, y)), logic.Mod(x, y)), x), Proved},
		// Guards against two quantifiers with the same variable name
		// being given the same witness. One number need not be both.
		{
			"two witnesses of one name are two numbers", Options{},
			[]*logic.Term{logic.Exists(bound, logic.Eq(bound, lit(1))), logic.Exists(bound, logic.Eq(bound, lit(2)))},
			logic.False(), Refuted,
		},
		{
			"two witnesses of one name in one formula", Options{},
			[]*logic.Term{logic.And(logic.Exists(bound, logic.Lt(bound, x)), logic.Exists(bound, logic.Lt(x, bound)))},
			logic.False(), Refuted,
		},
		// Guards against a proof being claimed when the resource limit is
		// reached: the goal is true and needs more than the limit allows.
		{"no effort left", Options{Effort: 1}, []*logic.Term{logic.Or(atMost(x), atMost(y)), logic.Lt(lit(0), x)}, atMost(y), Exhausted},
		{"effort enough", Options{}, []*logic.Term{logic.Or(atMost(x), atMost(y)), logic.Lt(lit(0), x)}, atMost(y), Proved},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got := z3.Prove(test.hyps, test.goal, test.opts)

			if got != test.want {
				t.Fatalf("Prove(%v, %v) = %v, want %v", test.hyps, test.goal, got, test.want)
			}
		})
	}
}

// TestWritesStayLinear checks that a chain of writes to one table, the
// shape memory has after a run of assignments, is encoded in text that
// grows with the number of writes and not with two to its power: each
// write mentions its table twice.
func TestWritesStayLinear(t *testing.T) {
	x := logic.Const("x", logic.Int)
	table := logic.Const("M", logic.SeqOf(logic.IntSeq))
	// Sixteen writes keep a wrong encoding to a few megabytes, so that it
	// fails quickly.
	for i := range 16 {
		table = logic.Write(table, x, logic.IntLit(int64(i)), logic.IntLit(int64(i)))
	}
	goal := logic.Eq(logic.Select(logic.Select(table, x), logic.IntLit(0)), logic.IntLit(0))
	_, script, _ := encode([]*logic.Term{logic.Not(goal)}, Options{})
	if len(script) > 16*1000 {
		t.Fatalf("a chain of 16 writes is encoded in %d bytes", len(script))
	}
	if result := solverFor(t).Prove(nil, goal, Options{}); result != Proved {
		t.Fatalf("the first write of a chain of 16 is not read back: %v", result)
	}
}

// solverFor returns the solver the tests use, which is Z3 of the pinned
// version on PATH. Without it the tests fail rather than skip: a test that
// is skipped where Z3 is missing would let a broken encoding pass.
func solverFor(t *testing.T) *Solver {
	t.Helper()
	s, err := New("")
	if err != nil {
		t.Fatal(err)
	}
	return s
}

// TestTranslation checks rules of the translation that the random problems
// of TestProveIsSound reach too rarely: each problem is one that a
// particular wrong version of a rule gets wrong, in one direction or the
// other.
func TestTranslation(t *testing.T) {
	z3 := solverFor(t)
	lit := logic.IntLit
	A := logic.Const("A", logic.IntSeq)
	lo, n, j, m := logic.Const("lo", logic.Int), logic.Const("n", logic.Int), logic.Const("j", logic.Int), logic.Const("m", logic.Int)
	k := logic.Bound("k", logic.Int)
	inRange := func(v, from, to *logic.Term) *logic.Term { return logic.And(logic.Le(from, v), logic.Lt(v, to)) }
	// A fact about the elements from lo on, and the same through a cut.
	shifted := logic.Forall(k, logic.Implies(inRange(k, lit(0), n), logic.Le(lit(0), logic.Select(A, logic.Add(k, lo)))))
	cut := logic.Subseq(A, lo, logic.Add(lo, n))
	throughCut := logic.Forall(k, logic.Implies(inRange(k, lit(0), logic.Len(cut)), logic.Le(lit(0), logic.Select(cut, k))))
	scaled := logic.Forall(k, logic.Implies(inRange(k, lit(0), n), logic.Eq(logic.Select(A, logic.Add(logic.Mul(lit(2), k), lo)), lit(0))))
	one, two := logic.Add(k, lit(1)), logic.Add(k, lit(2))
	twoShifts := logic.Forall(k, logic.Implies(inRange(k, lit(0), n), logic.Eq(logic.Select(A, one), logic.Sub(logic.Select(A, two), lit(5)))))
	backwards := logic.Forall(k, logic.Implies(inRange(k, lit(0), n), logic.Le(lit(0), logic.Select(A, logic.Sub(n, logic.Add(k, lit(1)))))))
	factored := logic.Forall(k, logic.Implies(inRange(k, lit(0), n), logic.Eq(logic.Select(A, logic.Mul(lit(2), logic.Add(k, lo))), lit(0))))
	doubled := logic.Forall(k, logic.Implies(inRange(k, lit(0), n), logic.Eq(logic.Select(A, logic.Mul(lit(2), k)), lit(0))))
	text := func(s string) *logic.Term { return logic.Bytes(s) }
	s, u := logic.Const("s", logic.IntSeq), logic.Const("u", logic.IntSeq)
	n2 := logic.Bound("n", logic.Int)
	halved := logic.And(logic.Lt(lit(1), n2), logic.Eq(logic.Mod(n2, lit(2)), lit(0)), logic.Pred("pow", logic.Div(n2, lit(2))))
	pow := Options{Preds: map[string]*logic.PredDef{"pow": {Name: "pow", Params: []*logic.Term{n2}, Body: logic.Or(logic.Eq(n2, lit(1)), halved)}}}
	x := logic.Const("x", logic.Int)
	e := logic.Bound("e", logic.Err)
	ea, eb, ec := logic.Const("ea", logic.Err), logic.Const("eb", logic.Err), logic.Const("ec", logic.Err)
	tests := []struct {
		name string
		opts Options
		hyps []*logic.Term
		goal *logic.Term
		want Result
	}{
		// Guards against facts whose index is moved never being used.
		{"a fact about moved indices", Options{}, []*logic.Term{shifted, inRange(j, lo, logic.Add(lo, n))}, logic.Le(lit(0), logic.Select(A, j)), Proved},
		{"a fact about moved indices stops at its end", Options{}, []*logic.Term{shifted, logic.Le(lit(0), n)}, logic.Le(lit(0), logic.Select(A, logic.Add(lo, n))), Refuted},
		{"a fact about a cut holds of the whole", Options{}, []*logic.Term{throughCut, logic.Le(lit(0), n), inRange(j, lo, logic.Add(lo, n))}, logic.Le(lit(0), logic.Select(A, j)), Proved},
		{"a fact about scaled indices", Options{}, []*logic.Term{scaled, inRange(j, lit(0), n), logic.Eq(m, logic.Add(logic.Mul(lit(2), j), lo))}, logic.Eq(logic.Select(A, m), lit(0)), Proved},
		{"a fact about scaled indices says nothing between them", Options{}, []*logic.Term{scaled, inRange(j, lit(0), n), logic.Eq(m, logic.Add(logic.Add(logic.Mul(lit(2), j), lo), lit(1)))}, logic.Eq(logic.Select(A, m), lit(0)), Refuted},
		// Guards against the copies of a fact with two moved reads of one
		// sequence, an offset under a negation, and an offset under a
		// factor getting their indices wrong.
		{"two moved reads of one sequence", Options{}, []*logic.Term{twoShifts, logic.Eq(n, lit(3)), logic.Eq(logic.Select(A, lit(2)), lit(5))}, logic.Eq(logic.Select(A, lit(3)), lit(10)), Proved},
		{"two moved reads of one sequence are consistent", Options{}, []*logic.Term{twoShifts, logic.Eq(n, lit(3)), logic.Eq(logic.Select(A, lit(2)), lit(5))}, logic.False(), Refuted},
		{"an offset under a negation", Options{}, []*logic.Term{backwards, inRange(j, lit(0), n)}, logic.Le(lit(0), logic.Select(A, j)), Proved},
		{"an offset under a negation stops at its end", Options{}, []*logic.Term{backwards, logic.Le(lit(0), n)}, logic.Le(lit(0), logic.Select(A, n)), Refuted},
		{"an offset under a factor", Options{}, []*logic.Term{factored, inRange(j, lit(0), n), logic.Eq(m, logic.Mul(lit(2), logic.Add(j, lo)))}, logic.Eq(logic.Select(A, m), lit(0)), Proved},
		{"an offset under a factor stops at its end", Options{}, []*logic.Term{factored, logic.Le(lit(0), n), logic.Eq(m, logic.Mul(lit(2), logic.Add(n, lo)))}, logic.Eq(logic.Select(A, m), lit(0)), Refuted},
		{"an offset under a factor is scaled", Options{}, []*logic.Term{factored, logic.Lt(lit(0), n), logic.Eq(m, logic.Add(logic.Mul(lit(2), lo), lit(1)))}, logic.Eq(logic.Select(A, m), lit(0)), Refuted},
		{"an offset under a factor is scaled with it", Options{}, []*logic.Term{factored, logic.Eq(lo, lit(1)), logic.Eq(n, lit(2))}, logic.Eq(logic.Select(A, lit(3)), lit(0)), Refuted},
		{"an offset under a factor reaches the last element", Options{}, []*logic.Term{factored, logic.Eq(lo, lit(1)), logic.Eq(n, lit(2)), logic.Eq(m, lit(4))}, logic.Eq(logic.Select(A, m), lit(0)), Proved},
		{"a scaled read without an offset", Options{}, []*logic.Term{doubled, inRange(j, lit(0), n), logic.Eq(m, logic.Mul(lit(2), j))}, logic.Eq(logic.Select(A, m), lit(0)), Proved},
		{"a scaled read without an offset says nothing between", Options{}, []*logic.Term{doubled, inRange(j, lit(0), n), logic.Eq(m, logic.Add(logic.Mul(lit(2), j), lit(1)))}, logic.Eq(logic.Select(A, m), lit(0)), Refuted},
		// Guards against a concatenation kept as a whole, such as one
		// stored in memory, holding the wrong element at the seam.
		{"the first element after the seam", Options{}, nil, logic.Eq(logic.Select(logic.Select(logic.Store(logic.Const("M", logic.SeqOf(logic.IntSeq)), lit(0), logic.Concat(text("ab"), text("c"))), lit(0)), lit(2)), lit('c')), Proved},
		{"the last element before the seam", Options{}, nil, logic.Eq(logic.Select(logic.Select(logic.Store(logic.Const("M", logic.SeqOf(logic.IntSeq)), lit(0), logic.Concat(text("ab"), text("c"))), lit(0)), lit(1)), lit('b')), Proved},
		// Guards against a division by zero and a remainder by zero being
		// tied to each other; the logic says nothing about either.
		{"a quotient by zero is not the remainder", Options{}, nil, logic.Eq(logic.Div(x, lit(0)), logic.Mod(x, lit(0))), Refuted},
		// Guards against keys that confuse sequences or tell equal ones
		// apart.
		{"equal texts have equal keys", Options{}, nil, logic.Eq(logic.Key(text("ab")), logic.Key(text("ab"))), Proved},
		{"different texts have different keys", Options{}, nil, logic.Ne(logic.Key(text("ab")), logic.Key(text("abc"))), Proved},
		{"texts of one length with other bytes have different keys", Options{}, nil, logic.Ne(logic.Key(text("ab")), logic.Key(text("ac"))), Proved},
		{"keys look only below the length", Options{}, nil, logic.Eq(logic.Key(logic.Store(logic.Fill(lit(1), lit(5)), lit(3), lit(9))), logic.Key(logic.Fill(lit(1), lit(5)))), Proved},
		{"sequences with the same elements have the same key", Options{}, []*logic.Term{logic.Eq(logic.Len(s), lit(1)), logic.Eq(logic.Len(u), lit(1)), logic.Eq(logic.Select(s, lit(0)), logic.Select(u, lit(0)))}, logic.Eq(logic.Key(s), logic.Key(u)), Proved},
		{"sequences of one length may have different keys", Options{}, []*logic.Term{logic.Eq(logic.Len(s), lit(1)), logic.Eq(logic.Len(u), lit(1))}, logic.Eq(logic.Key(s), logic.Key(u)), Refuted},
		// Guards against a number past 64 bits being cut on its way to Z3.
		{"a number past 64 bits", Options{}, nil, logic.Lt(lit(0), logic.BigLit(new(big.Int).Lsh(big.NewInt(1), 64))), Proved},
		{"a number past 64 bits is not zero", Options{}, nil, logic.Eq(logic.BigLit(new(big.Int).Lsh(big.NewInt(1), 64)), lit(0)), Refuted},
		// Guards against a recursive predicate that is not unfolded, or
		// unfolded wrongly.
		{"a recursive predicate holds where its body does", pow, nil, logic.Pred("pow", lit(8)), Proved},
		{"a recursive predicate fails where its body does", pow, nil, logic.Not(logic.Pred("pow", lit(6))), Proved},
		{"a recursive predicate does not hold of everything", pow, nil, logic.Pred("pow", lit(6)), Refuted},
		{"an odd power of two is one", pow, []*logic.Term{logic.Pred("pow", x), logic.Eq(logic.Mod(x, lit(2)), lit(1))}, logic.Eq(x, lit(1)), Proved},
		// Guards against a model in which every error is nil.
		{"some error is not nil", Options{}, nil, logic.Not(logic.Forall(e, logic.IsNil(e))), Proved},
		// Guards against errors being told apart only by whether they are
		// nil, which would make every two non-nil errors the same, and
		// against is being written as equality or as anything that holds
		// or fails of every two errors.
		{"two errors that are not nil may differ", Options{}, []*logic.Term{logic.Not(logic.IsNil(ea)), logic.Not(logic.IsNil(eb))}, logic.Eq(ea, eb), Refuted},
		{"two errors that are not nil may be the same", Options{}, []*logic.Term{logic.Not(logic.IsNil(ea)), logic.Not(logic.IsNil(eb))}, logic.Not(logic.Eq(ea, eb)), Refuted},
		{"an error equal to a nil one is nil", Options{}, []*logic.Term{logic.Eq(ea, eb), logic.IsNil(eb)}, logic.IsNil(ea), Proved},
		{"is is not equality", Options{}, []*logic.Term{logic.Not(logic.Eq(ea, eb))}, logic.Not(logic.Is(ea, eb)), Refuted},
		{"is may differ from equality the other way", Options{}, []*logic.Term{logic.Eq(ea, eb)}, logic.Is(ea, eb), Refuted},
		{"is is not symmetric", Options{}, []*logic.Term{logic.Is(ea, eb)}, logic.Is(eb, ea), Refuted},
		{"is is a function of the two errors", Options{}, []*logic.Term{logic.Eq(ea, ec), logic.Is(ea, eb)}, logic.Is(ec, eb), Proved},
		{"is is a function of its target", Options{}, []*logic.Term{logic.Eq(eb, ec), logic.Is(ea, eb)}, logic.Is(ea, ec), Proved},
		{"is depends on its target", Options{}, []*logic.Term{logic.Is(ea, eb)}, logic.Is(ea, ec), Refuted},
		{"is depends on the error", Options{}, []*logic.Term{logic.Is(ea, eb)}, logic.Is(ec, eb), Refuted},
		// Guards against the reference of an error being anything but a
		// function of it: a constant, which would make every error hold the
		// same value; injective, which would make two errors that hold equal
		// values differ; or the same function as is.
		{"the reference of an error is a function of it", Options{}, []*logic.Term{logic.Eq(ea, eb)}, logic.Eq(logic.ErrRef(ea), logic.ErrRef(eb)), Proved},
		{"two errors may have two references", Options{}, nil, logic.Eq(logic.ErrRef(ea), logic.ErrRef(eb)), Refuted},
		{"two errors may have one reference", Options{}, []*logic.Term{logic.Not(logic.Eq(ea, eb))}, logic.Ne(logic.ErrRef(ea), logic.ErrRef(eb)), Refuted},
		{"two references tell two errors apart", Options{}, []*logic.Term{logic.Ne(logic.ErrRef(ea), logic.ErrRef(eb))}, logic.Not(logic.Eq(ea, eb)), Proved},
		{"the reference of nil is not known", Options{}, nil, logic.Eq(logic.ErrRef(logic.NilErr()), logic.RefLit(0)), Refuted},
		{"a table read at the reference of an error follows the error", Options{}, []*logic.Term{logic.Eq(ea, eb), logic.Eq(logic.Select(A, logic.ErrRef(ea)), lit(3))},
			logic.Eq(logic.Select(A, logic.ErrRef(eb)), lit(3)), Proved},
		// Guards against a predicate written out in place capturing a
		// variable bound around its application.
		{"an inlined predicate does not capture", Options{Preds: map[string]*logic.PredDef{"some": {Name: "some", Params: []*logic.Term{n2}, Body: logic.Exists(k, logic.Lt(n2, k))}}},
			nil, logic.Forall(k, logic.Pred("some", k)), Proved},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// Only whether the goal is proved matters; a goal that is not
			// may be refuted or left open.
			if got := z3.Prove(test.hyps, test.goal, test.opts); (got == Proved) != (test.want == Proved) {
				t.Fatalf("Prove(%v, %v) = %v, want %v", test.hyps, test.goal, got, test.want)
			}
		})
	}
}

// TestManyWrites checks that the chain of tactics proves what a field
// written through many pointers that may be the same holds afterwards, the
// shape of a function that sets one field of many structs. ctx-simplify,
// which the chain had, used the whole resource limit on these goals.
func TestManyWrites(t *testing.T) {
	z3 := solverFor(t)
	lit := logic.IntLit
	const n = 10
	table := logic.Const("M", logic.SeqOf(logic.IntSeq))
	var hyps []*logic.Term
	refs, ats := make([]*logic.Term, n), make([]*logic.Term, n)
	for i := range n {
		refs[i], ats[i] = logic.Const(fmt.Sprintf("p%d", i), logic.Ref), logic.Const(fmt.Sprintf("a%d", i), logic.Int)
		hyps = append(hyps, logic.Lt(lit(0), refs[i]), logic.Le(lit(0), ats[i]))
	}
	for i := range n {
		table = logic.Write(table, refs[i], ats[i], lit(1))
	}
	for i := range n {
		read := logic.Eq(logic.Select(logic.Select(table, refs[i]), ats[i]), lit(1))
		if got := z3.Prove(hyps, read, Options{}); got != Proved {
			t.Errorf("the field written through p%d is not read back after %d writes: %v", i, n, got)
		}
		hyps = append(hyps, read)
	}
}

// TestExtensionality checks when the axiom of extensionality is left out:
// only where a sequence of sequences of sequences is declared, and never
// where a key function or a recursive predicate takes a sequence, since
// those can tell apart two sequences that only the axiom makes equal. Each
// problem that needs the axiom also declares such a sequence, so that it is
// the second condition alone that keeps the axiom.
func TestExtensionality(t *testing.T) {
	z3 := solverFor(t)
	lit := logic.IntLit
	x, y, n := logic.Const("x", logic.Int), logic.Const("y", logic.Int), logic.Const("n", logic.Int)
	A := logic.Const("A", logic.IntSeq)
	M := logic.Const("M", logic.SeqOf(logic.IntSeq))
	// Strings held in a region, as the strings of a struct field are.
	deep := logic.Le(lit(0), logic.Len(logic.Select(logic.Select(logic.Const("D", logic.SeqOf(logic.SeqOf(logic.IntSeq))), x), y)))
	s := logic.Bound("s", logic.IntSeq)
	// A recursive predicate of a sequence: every element from the first
	// on is at least zero, read through a cut.
	rest := logic.Subseq(s, lit(1), logic.Len(s))
	nonneg := Options{Preds: map[string]*logic.PredDef{"nonneg": {Name: "nonneg", Params: []*logic.Term{s},
		Body: logic.Or(logic.Eq(logic.Len(s), lit(0)), logic.And(logic.Le(lit(0), logic.Select(s, lit(0))), logic.Pred("nonneg", rest)))}}}
	k := logic.Bound("k", logic.Int)
	keyed := logic.Forall(k, logic.Implies(logic.And(logic.Le(lit(0), k), logic.Lt(k, n)), logic.Eq(logic.Key(logic.Select(M, k)), lit(7))))
	tests := []struct {
		name    string
		opts    Options
		hyps    []*logic.Term
		goal    *logic.Term
		without bool
	}{
		// Guards against the axiom being left out where a predicate tells
		// sequences apart: Store(A, x, y) is A only by extensionality.
		{"a recursive predicate of a sequence that a write left as it was", nonneg,
			[]*logic.Term{deep, logic.Pred("nonneg", A), logic.Eq(logic.Select(A, x), y)}, logic.Pred("nonneg", logic.Store(A, x, y)), false},
		// Guards against the axiom being left out where a key inside a
		// quantifier tells sequences apart.
		{"a key inside a quantifier of a sequence that a write left as it was", Options{},
			[]*logic.Term{deep, keyed, logic.Lt(lit(0), n), logic.Eq(logic.Select(logic.Select(M, lit(0)), x), y)},
			logic.Eq(logic.Key(logic.Store(logic.Select(M, lit(0)), x, y)), lit(7)), false},
		// Guards against the axiom being kept where nothing tells
		// sequences apart, and against reads through writes being lost
		// without it.
		{"a region of strings without a key", Options{}, []*logic.Term{deep}, logic.Eq(logic.Select(logic.Select(logic.Write(M, x, y, lit(5)), x), y), lit(5)), true},
		{"a region of strings beside a write elsewhere", Options{}, []*logic.Term{deep, logic.Ne(x, y)},
			logic.Eq(logic.Select(logic.Select(logic.Write(M, x, y, lit(5)), y), y), logic.Select(logic.Select(M, y), y)), true},
		{"no region of strings", Options{}, nil, logic.Eq(logic.Select(logic.Select(logic.Write(M, x, y, lit(5)), x), y), lit(5)), false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			script := Script([]*logic.Term{logic.And(append(slices.Clip(test.hyps), logic.Not(test.goal))...)}, test.opts)
			if without := strings.Contains(script, "array.extensional false"); without != test.without {
				t.Fatalf("the problem is solved without extensionality: %v, want %v\n%s", without, test.without, script)
			}
			if got := z3.Prove(test.hyps, test.goal, test.opts); got != Proved {
				t.Fatalf("Prove(%v, %v) = %v, want proved", test.hyps, test.goal, got)
			}
		})
	}
}
