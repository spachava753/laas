package vego

import (
	"errors"
	"fmt"
	"math/big"
	"math/rand"
	"slices"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// evaluator computes the value of ground terms, which is how the tests of
// trusted contracts check a contract against what a real function did. Each
// quantifier ranges over exactly the integers its guards allow, which the
// resolver writes as comparisons of the bound variable, so no sample is
// checked on a prefix of its interval; a quantifier without a lower and an
// upper guard, or over more than maxRange integers, panics.
type evaluator struct {
	bindings map[string]*big.Int
	errors   *grounder
	// callbacks answers, by the name of the sequence that stands for a
	// function a contract applies, what the function returns.
	callbacks map[string]func(int64) int64
}

// maxRange is the most integers a quantifier of a sample may range over.
const maxRange = 1 << 20

func (e *evaluator) number(t *logic.Term) *big.Int {
	x := func(i int) *big.Int { return e.number(t.Args[i]) }
	switch t.Op {
	case logic.OpIntLit:
		return t.Value()
	case logic.OpTrue, logic.OpFalse:
		// An element of a sequence of booleans, which holds reads as a
		// number that is not zero.
		if t.Op == logic.OpTrue {
			return big.NewInt(1)
		}
		return big.NewInt(0)
	case logic.OpBound:
		value, bound := e.bindings[t.Name]
		if !bound {
			panic("the bound variable " + t.Name + " has no value here")
		}
		return value
	case logic.OpAdd:
		return new(big.Int).Add(x(0), x(1))
	case logic.OpMul:
		return new(big.Int).Mul(x(0), x(1))
	case logic.OpNeg:
		return new(big.Int).Neg(x(0))
	case logic.OpDiv, logic.OpMod:
		divisor := x(1)
		if divisor.Sign() == 0 {
			panic("a formula of a sample divides by zero: " + t.String())
		}
		// Quo and Rem truncate toward zero, as Go's / and % do.
		if t.Op == logic.OpDiv {
			return new(big.Int).Quo(x(0), divisor)
		}
		return new(big.Int).Rem(x(0), divisor)
	case logic.OpLen:
		if t.Args[0].Sort == logic.SeqOf(logic.IntSeq) {
			return big.NewInt(int64(len(e.rows(t.Args[0]))))
		}
		return big.NewInt(int64(len(e.sequence(t.Args[0]))))
	case logic.OpIte:
		if e.holds(t.Args[0]) {
			return x(1)
		}
		return x(2)
	case logic.OpSelect:
		if answer, ok := e.callbacks[t.Args[0].Name]; ok && t.Args[0].Op == logic.OpConst {
			return big.NewInt(answer(x(1).Int64()))
		}
		elements, index := e.sequence(t.Args[0]), x(1)
		if index.Sign() < 0 || index.Cmp(big.NewInt(int64(len(elements)))) >= 0 {
			// Outside a sequence the logic leaves the value open in some
			// places and not in others: past the end of a substring is
			// its parent's byte. A formula that reads there is one the
			// evaluator cannot judge.
			panic(fmt.Sprintf("a formula reads %s at %s, outside its %d elements: %s", t.Args[0], index, len(elements), t))
		}
		return elements[index.Int64()]
	}
	panic("cannot evaluate number " + t.String())
}

func (e *evaluator) sequence(t *logic.Term) []*big.Int {
	switch t.Op {
	case logic.OpSelect:
		rows, index := e.rows(t.Args[0]), e.number(t.Args[1])
		if index.Sign() < 0 || index.Cmp(big.NewInt(int64(len(rows)))) >= 0 {
			panic(fmt.Sprintf("a formula reads %s at %s, outside its %d elements: %s", t.Args[0], index, len(rows), t))
		}
		return rows[index.Int64()]
	case logic.OpFill:
		return slices.Repeat([]*big.Int{e.number(t.Args[1])}, int(e.number(t.Args[0]).Int64()))
	case logic.OpPush:
		// A ground sequence is a chain of pushes onto a fill, which is
		// walked once: copying the sequence at every push would make a
		// long one cost the square of its length.
		pushed := pushes(t)
		elements := slices.Clone(e.sequence(pushed[len(pushed)-1].Args[0]))
		for _, push := range slices.Backward(pushed) {
			elements = append(elements, e.number(push.Args[1]))
		}
		return elements
	}
	panic("cannot evaluate sequence " + t.String())
}

// rows computes a sequence of sequences, such as the strings of a
// []string.
func (e *evaluator) rows(t *logic.Term) [][]*big.Int {
	switch t.Op {
	case logic.OpFill:
		return slices.Repeat([][]*big.Int{e.sequence(t.Args[1])}, int(e.number(t.Args[0]).Int64()))
	case logic.OpPush:
		pushed := pushes(t)
		rows := slices.Clone(e.rows(pushed[len(pushed)-1].Args[0]))
		for _, push := range slices.Backward(pushed) {
			rows = append(rows, e.sequence(push.Args[1]))
		}
		return rows
	}
	panic("cannot evaluate sequence of sequences " + t.String())
}

// pushes returns the chain of pushes that t starts, from the last push to
// the first; the sequence the first one pushes onto is not a push.
func pushes(t *logic.Term) []*logic.Term {
	var chain []*logic.Term
	for ; t.Op == logic.OpPush; t = t.Args[0] {
		chain = append(chain, t)
	}
	return chain
}

func (e *evaluator) holds(t *logic.Term) bool {
	x := func(i int) bool { return e.holds(t.Args[i]) }
	switch t.Op {
	case logic.OpTrue, logic.OpFalse:
		return t.Op == logic.OpTrue
	case logic.OpEq:
		// The resolver writes = of booleans as an iff and of sequences as
		// a quantified formula, so only numbers and errors come here.
		if t.Args[0].Sort == logic.Err {
			return e.errors.error(t.Args[0]) == e.errors.error(t.Args[1])
		}
		return e.number(t.Args[0]).Cmp(e.number(t.Args[1])) == 0
	case logic.OpIs:
		return errors.Is(e.errors.error(t.Args[0]), e.errors.error(t.Args[1]))
	case logic.OpLe:
		return e.number(t.Args[0]).Cmp(e.number(t.Args[1])) <= 0
	case logic.OpLt:
		return e.number(t.Args[0]).Cmp(e.number(t.Args[1])) < 0
	case logic.OpNot:
		return !x(0)
	case logic.OpImplies:
		return !x(0) || x(1)
	case logic.OpIff:
		return x(0) == x(1)
	case logic.OpAnd:
		return !slices.ContainsFunc(t.Args, func(arg *logic.Term) bool { return !e.holds(arg) })
	case logic.OpOr:
		return slices.ContainsFunc(t.Args, e.holds)
	case logic.OpIsNil:
		return e.errors.error(t.Args[0]) == nil
	case logic.OpSelect:
		return e.number(t).Sign() != 0
	case logic.OpForall, logic.OpExists:
		name := t.Args[0].Name
		lo, hi := e.rangeOf(t)
		saved, wasBound := e.bindings[name]
		defer func() {
			if wasBound {
				e.bindings[name] = saved
			} else {
				delete(e.bindings, name)
			}
		}()
		for index := lo; index <= hi; index++ {
			e.bindings[name] = big.NewInt(index)
			if e.holds(t.Args[1]) == (t.Op == logic.OpExists) {
				return t.Op == logic.OpExists
			}
		}
		return t.Op == logic.OpForall
	}
	panic("cannot evaluate formula " + t.String())
}

// judge reports whether a formula holds of a sample, and fails the test
// with what the evaluator could not judge, such as a read outside a
// sequence.
func (e *evaluator) judge(t *testing.T, what string, formula *logic.Term) (holds bool) {
	t.Helper()
	defer func() {
		if fault := recover(); fault != nil {
			t.Fatalf("%s cannot be judged on this sample: %v", what, fault)
		}
	}()
	return e.holds(formula)
}

// rangeOf returns the integers, lo to hi inclusive, that the variable of
// a quantifier ranges over: the guards the resolver writes for an interval,
// the antecedent of a Forall's body and the conjuncts of an Exists's,
// found also below quantifiers of the same kind that share the guards, as
// in Forall i, j in [0, n). Every comparison found narrows the range, which
// changes nothing of the value, since outside it the body of a Forall is
// true and that of an Exists false. Only comparisons whose other side can
// be evaluated here are used.
func (e *evaluator) rangeOf(q *logic.Term) (int64, int64) {
	v := q.Args[0]
	var lo, hi *big.Int
	var guards []*logic.Term
	// conjuncts adds the comparisons among the conjuncts of t, going on
	// into a quantifier of q's kind when inner is set.
	var conjuncts func(t *logic.Term, inner bool)
	// collect adds the guards of a quantifier of q's kind.
	collect := func(t *logic.Term) {}
	conjuncts = func(t *logic.Term, inner bool) {
		switch {
		case t.Op == logic.OpAnd:
			for _, arg := range t.Args {
				conjuncts(arg, inner)
			}
		case t.Op == logic.OpLe || t.Op == logic.OpLt:
			guards = append(guards, t)
		case inner && t.Op == q.Op:
			collect(t)
		}
	}
	collect = func(t *logic.Term) {
		body := t.Args[1]
		switch {
		case q.Op == logic.OpExists:
			conjuncts(body, true)
		case body.Op == logic.OpImplies:
			conjuncts(body.Args[0], false)
			if body.Args[1].Op == logic.OpForall {
				collect(body.Args[1])
			}
		case body.Op == logic.OpForall:
			collect(body)
		}
	}
	collect(q)
	isVar := func(t *logic.Term) bool { return t.Op == logic.OpBound && t.Name == v.Name }
	for _, g := range guards {
		left, right := g.Args[0], g.Args[1]
		switch {
		case isVar(right) && !isVar(left) && e.evaluable(left):
			bound := e.number(left)
			if g.Op == logic.OpLt {
				bound = new(big.Int).Add(bound, big.NewInt(1))
			}
			if lo == nil || bound.Cmp(lo) > 0 {
				lo = bound
			}
		case isVar(left) && !isVar(right) && e.evaluable(right):
			bound := e.number(right)
			if g.Op == logic.OpLt {
				bound = new(big.Int).Sub(bound, big.NewInt(1))
			}
			if hi == nil || bound.Cmp(hi) < 0 {
				hi = bound
			}
		}
	}
	if lo == nil || hi == nil {
		panic(fmt.Sprintf("the quantifier over %s has no interval that a sample can range over: %s", v.Name, q))
	}
	if hi.Cmp(lo) < 0 {
		return 0, -1
	}
	if new(big.Int).Sub(hi, lo).Cmp(big.NewInt(maxRange)) > 0 {
		panic(fmt.Sprintf("the quantifier over %s ranges over %s to %s, more than a sample can check: %s", v.Name, lo, hi, q))
	}
	return lo.Int64(), hi.Int64()
}

// evaluable reports whether a term mentions only bound variables that have
// a value here.
func (e *evaluator) evaluable(t *logic.Term) bool {
	if t.Op == logic.OpBound {
		_, bound := e.bindings[t.Name]
		return bound
	}
	for _, arg := range t.Args {
		if !e.evaluable(arg) {
			return false
		}
	}
	return true
}

// groundEnv gives a formula's names ground values: a name is a number or a
// sequence, read by its length and its elements.
type groundEnv map[string]*logic.Term

func (e groundEnv) Path(root string, steps []logic.Step, _ logic.When) (*logic.Term, error) {
	value, ok := e[root]
	if !ok {
		return nil, fmt.Errorf("no value for %s", root)
	}
	for _, step := range steps {
		switch {
		case step.Len:
			value = logic.Len(value)
		case step.Index != nil:
			value = logic.Select(value, step.Index)
		default:
			return nil, fmt.Errorf("the test reads only lengths and elements")
		}
	}
	return value, nil
}

func (groundEnv) Relation(name string, _ []logic.Path) (*logic.Term, error) {
	return nil, fmt.Errorf("no %s here", name)
}

func (groundEnv) Qualified(path, name string, _ []logic.Step, _ logic.When) (*logic.Term, error) {
	return nil, fmt.Errorf("no %s.%s here", path, name)
}

// ints is the ground sequence of numbers.
func ints(values ...int64) *logic.Term {
	seq := logic.Fill(logic.IntLit(0), logic.IntLit(0))
	for _, v := range values {
		seq = logic.Push(seq, logic.IntLit(v))
	}
	return seq
}

// TestEvaluator checks the evaluator that the tests of trusted contracts
// rest on against Go on random values: each kind of interval, a value that
// makes a formula false only at its first or last index, quantifiers
// nested and sharing an interval, a range of elements, Go's / and %, and
// numbers past int64. A quantifier the evaluator cannot bound, and a read
// outside a sequence, panic.
func TestEvaluator(t *testing.T) {
	parallel(t)
	res := logic.NewResolver()
	eval := func(src string, env groundEnv) bool {
		t.Helper()
		node, err := logic.ParseFormula(src)
		if err != nil {
			t.Fatalf("parse %q: %v", src, err)
		}
		formula, err := res.Formula(node, env)
		if err != nil {
			t.Fatalf("resolve %q: %v", src, err)
		}
		return (&evaluator{bindings: map[string]*big.Int{}}).holds(formula)
	}
	rng := rand.New(rand.NewSource(1))
	for range 2000 {
		values := make([]int64, rng.Intn(7))
		for i := range values {
			values[i] = int64(rng.Intn(5))
		}
		lo, hi, x := int64(rng.Intn(9)-2), int64(rng.Intn(9)-2), int64(rng.Intn(5))
		env := groundEnv{"A": ints(values...), "lo": logic.IntLit(lo), "hi": logic.IntLit(hi), "x": logic.IntLit(x)}
		// A read outside A cannot be judged, so the formulas read A only
		// inside it, and Go's answer counts only those indices.
		inside := func(k int64) bool { return 0 <= k && k < int64(len(values)) }
		// Go's answer over the integers from first to last.
		every := func(first, last int64, p func(int64) bool) bool {
			for k := first; k <= last; k++ {
				if !p(k) {
					return false
				}
			}
			return true
		}
		below := func(k int64) bool { return !inside(k) || values[k] < x }
		for _, interval := range []struct {
			text        string
			first, last int64
		}{
			{"[lo, hi)", lo, hi - 1}, {"[lo, hi]", lo, hi}, {"(lo, hi)", lo + 1, hi - 1}, {"(lo, hi]", lo + 1, hi},
		} {
			if got, want := eval("Forall k in "+interval.text+" : (0 <= k And k < |A|) -> A[k] < x", env), every(interval.first, interval.last, below); got != want {
				t.Fatalf("Forall k in %s : A[k] < x with A = %v, lo = %d, hi = %d, x = %d: got %v, want %v", interval.text, values, lo, hi, x, got, want)
			}
			if got, want := eval("Exists k in "+interval.text+" : 0 <= k And k < |A| And ~(A[k] < x)", env), !every(interval.first, interval.last, below); got != want {
				t.Fatalf("Exists k in %s : ~(A[k] < x) with A = %v, lo = %d, hi = %d, x = %d: got %v, want %v", interval.text, values, lo, hi, x, got, want)
			}
		}
		n := int64(len(values))
		sorted := slices.IsSorted(values)
		if got := eval("Forall i in [0, |A|) : Forall j in [i, |A|) : A[i] <= A[j]", env); got != sorted {
			t.Fatalf("sorted %v: got %v", values, got)
		}
		if got := eval("Forall i, j in [0, |A|) : i < j -> A[i] <= A[j]", env); got != sorted {
			t.Fatalf("sorted with a shared interval %v: got %v", values, got)
		}
		if got, want := eval("Exists i, j in [0, |A|) : i < j And A[j] < A[i]", env), !sorted; got != want {
			t.Fatalf("unsorted with a shared interval %v: got %v", values, got)
		}
		from, to := int64(rng.Intn(len(values)+1)), int64(rng.Intn(len(values)+1))
		env["from"], env["to"] = logic.IntLit(from), logic.IntLit(to)
		if got, want := eval("A[from:to) < x", env), every(from, to-1, below); got != want {
			t.Fatalf("A[from:to) < x with A = %v, from = %d, to = %d, x = %d: got %v, want %v", values, from, to, x, got, want)
		}
		if got, want := eval("Exists i in [0, |A|) : Forall j in [0, |A|) : A[j] <= A[i]", env), n > 0; got != want {
			t.Fatalf("a greatest element of %v: got %v", values, got)
		}
		if y := lo - 2; y != 0 {
			q, r := hi/y, hi%y
			if !eval(fmt.Sprintf("hi / (lo - 2) = %d And hi %% (lo - 2) = %d", q, r), env) {
				t.Fatalf("%d / %d is %d and %% is %d in Go, which the evaluator does not give", hi, y, q, r)
			}
			if eval(fmt.Sprintf("hi / (lo - 2) = %d Or hi %% (lo - 2) = %d", q+1, r+1), env) {
				t.Fatalf("the evaluator gives %d / %d another value", hi, y)
			}
		}
	}
	// Pushes onto a fill that is not empty come after it, in order, and a
	// long sequence keeps every element where it was pushed.
	onFill := logic.Push(logic.Push(logic.Fill(logic.IntLit(2), logic.IntLit(7)), logic.IntLit(1)), logic.IntLit(2))
	if !eval("|A| = 4 And A[0] = 7 And A[1] = 7 And A[2] = 1 And A[3] = 2", groundEnv{"A": onFill}) {
		t.Fatalf("pushes onto a fill of two 7s are not 7 7 1 2")
	}
	long := make([]int64, 500)
	for i := range long {
		long[i] = int64(i)
	}
	if !eval("|A| = 500 And Forall k in [0, |A|) : A[k] = k", groundEnv{"A": ints(long...)}) {
		t.Fatalf("a sequence of 500 pushes does not hold its elements where they were pushed")
	}
	huge := groundEnv{"u": logic.BigLit(new(big.Int).SetUint64(1<<64 - 1))}
	if !eval("u > 9223372036854775807 And u = 18446744073709551615 And u + 1 > 18446744073709551615 And u / 2 = 9223372036854775807", huge) {
		t.Fatalf("MaxUint64 is not evaluated as itself")
	}
	for _, src := range []string{"Forall k in Z : k = k", "Exists k in [0, 1 + 4096 * 4096) : A[k] < 0", "A[1] = 1", "A[-1] = 1", "Forall k in [0, |A|] : A[k] = 1"} {
		func() {
			defer func() {
				if recover() == nil {
					t.Errorf("%s was evaluated, though it reads outside A or ranges over integers no sample can", src)
				}
			}()
			eval(src, groundEnv{"A": ints(1)})
		}()
	}
}
