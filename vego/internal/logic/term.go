// Package logic defines the first-order specification language used by vego:
// its terms, the parser for //@ annotation clauses, and the resolver that
// turns parsed clauses into typed terms.
package logic

import (
	"strconv"
	"strings"
)

// Sort is the type of a logical term.
type Sort int

// The sorts of the logic. Integers are mathematical (unbounded) integers and
// sequences are the value model of Go slices.
const (
	Int Sort = iota
	Bool
	IntSeq
	BoolSeq
)

// IsSeq reports whether the sort is a sequence sort.
func (s Sort) IsSeq() bool { return s == IntSeq || s == BoolSeq }

// Elem returns the element sort of a sequence sort.
func (s Sort) Elem() Sort {
	if s == BoolSeq {
		return Bool
	}
	return Int
}

// SeqOf returns the sequence sort with the given element sort.
func SeqOf(elem Sort) Sort {
	if elem == Bool {
		return BoolSeq
	}
	return IntSeq
}

// String returns the Go-flavoured name of the sort.
func (s Sort) String() string {
	return [...]string{"int", "bool", "[]int", "[]bool"}[s]
}

// Op identifies the head symbol of a term.
type Op int

// Term operators. Quantifiers store the bound variable in Args[0] and the body
// in Args[1].
const (
	OpIntLit Op = iota
	OpTrue
	OpFalse
	OpConst // free symbolic constant (a program value)
	OpBound // quantifier-bound variable or predicate parameter
	OpAdd
	OpMul
	OpNeg
	OpDiv // Go division: truncates toward zero
	OpMod // Go remainder: takes the sign of the dividend
	OpLen
	OpSelect // Select(seq, index)
	OpStore  // Store(seq, index, value)
	OpFill   // Fill(length, value): a sequence holding one value everywhere
	OpPush   // Push(seq, value): seq with value appended
	OpIte
	OpEq
	OpLe
	OpLt
	OpAnd
	OpOr
	OpNot
	OpImplies
	OpIff
	OpForall
	OpExists
	OpPred
)

// Term is a node of a logical term or formula. Formulas are terms of sort
// Bool. Terms are immutable once built and may share structure.
type Term struct {
	Op   Op
	Sort Sort
	Name string // OpConst, OpBound, OpPred
	Val  int64  // OpIntLit
	Args []*Term
}

var (
	trueTerm  = &Term{Op: OpTrue, Sort: Bool}
	falseTerm = &Term{Op: OpFalse, Sort: Bool}
)

// True returns the true formula.
func True() *Term { return trueTerm }

// False returns the false formula.
func False() *Term { return falseTerm }

// BoolLit returns the formula for a boolean literal.
func BoolLit(v bool) *Term {
	if v {
		return trueTerm
	}
	return falseTerm
}

// IntLit returns an integer literal.
func IntLit(v int64) *Term { return &Term{Op: OpIntLit, Sort: Int, Val: v} }

// Const returns a free symbolic constant.
func Const(name string, sort Sort) *Term { return &Term{Op: OpConst, Sort: sort, Name: name} }

// Bound returns a bound variable. Names of bound variables must be unique
// within any formula they are nested in.
func Bound(name string, sort Sort) *Term { return &Term{Op: OpBound, Sort: sort, Name: name} }

func node(op Op, sort Sort, args ...*Term) *Term { return &Term{Op: op, Sort: sort, Args: args} }

// Add returns a + b.
func Add(a, b *Term) *Term { return node(OpAdd, Int, a, b) }

// Sub returns a - b.
func Sub(a, b *Term) *Term { return node(OpAdd, Int, a, Neg(b)) }

// Mul returns a * b.
func Mul(a, b *Term) *Term { return node(OpMul, Int, a, b) }

// Neg returns -a.
func Neg(a *Term) *Term { return node(OpNeg, Int, a) }

// Div returns the truncated quotient a / b.
func Div(a, b *Term) *Term { return node(OpDiv, Int, a, b) }

// Mod returns the remainder a % b.
func Mod(a, b *Term) *Term { return node(OpMod, Int, a, b) }

// Len returns the length of a sequence.
func Len(seq *Term) *Term { return node(OpLen, Int, seq) }

// Select returns seq[index].
func Select(seq, index *Term) *Term { return node(OpSelect, seq.Sort.Elem(), seq, index) }

// Store returns seq with the element at index replaced by value.
func Store(seq, index, value *Term) *Term { return node(OpStore, seq.Sort, seq, index, value) }

// Fill returns a sequence of the given length whose elements all equal value.
func Fill(length, value *Term) *Term { return node(OpFill, SeqOf(value.Sort), length, value) }

// Push returns seq with value appended.
func Push(seq, value *Term) *Term { return node(OpPush, seq.Sort, seq, value) }

// Ite returns the conditional term "if cond then a else b".
func Ite(cond, a, b *Term) *Term { return node(OpIte, a.Sort, cond, a, b) }

// Eq returns a = b for two terms of the same non-sequence sort.
func Eq(a, b *Term) *Term {
	if a.Sort == Bool {
		return Iff(a, b)
	}
	return node(OpEq, Bool, a, b)
}

// Le returns a <= b.
func Le(a, b *Term) *Term { return node(OpLe, Bool, a, b) }

// Lt returns a < b.
func Lt(a, b *Term) *Term { return node(OpLt, Bool, a, b) }

// Ne returns a != b.
func Ne(a, b *Term) *Term { return Not(Eq(a, b)) }

// And returns the conjunction of its arguments, flattening nested
// conjunctions and dropping trivial conjuncts.
func And(args ...*Term) *Term { return junction(OpAnd, args) }

// Or returns the disjunction of its arguments, flattening nested disjunctions
// and dropping trivial disjuncts.
func Or(args ...*Term) *Term { return junction(OpOr, args) }

// junction builds a flattened conjunction or disjunction. The unit element of
// the operator is dropped and the absorbing element short-circuits the result.
func junction(op Op, args []*Term) *Term {
	unit, absorbing := OpTrue, OpFalse
	if op == OpOr {
		unit, absorbing = OpFalse, OpTrue
	}
	var flat []*Term
	for _, arg := range args {
		switch arg.Op {
		case unit:
		case absorbing:
			return arg
		case op:
			flat = append(flat, arg.Args...)
		default:
			flat = append(flat, arg)
		}
	}
	switch len(flat) {
	case 0:
		return BoolLit(op == OpAnd)
	case 1:
		return flat[0]
	}
	return node(op, Bool, flat...)
}

// Not returns the negation of a formula.
func Not(a *Term) *Term {
	switch a.Op {
	case OpTrue:
		return falseTerm
	case OpFalse:
		return trueTerm
	case OpNot:
		return a.Args[0]
	}
	return node(OpNot, Bool, a)
}

// Implies returns a -> b.
func Implies(a, b *Term) *Term { return node(OpImplies, Bool, a, b) }

// Iff returns a <-> b.
func Iff(a, b *Term) *Term { return node(OpIff, Bool, a, b) }

// Forall returns the universal quantification of body over the bound variable.
func Forall(bound, body *Term) *Term { return node(OpForall, Bool, bound, body) }

// Exists returns the existential quantification of body over the bound variable.
func Exists(bound, body *Term) *Term { return node(OpExists, Bool, bound, body) }

// Pred returns the application of a user-defined predicate.
func Pred(name string, args ...*Term) *Term {
	return &Term{Op: OpPred, Sort: Bool, Name: name, Args: args}
}

// Conjuncts returns the top-level conjuncts of a formula.
func Conjuncts(t *Term) []*Term {
	if t.Op == OpAnd {
		return t.Args
	}
	return []*Term{t}
}

// Subst replaces bound variables by name. Replacement terms must not contain
// bound variables, which makes the substitution capture-free.
func Subst(t *Term, bindings map[string]*Term) *Term {
	if t.Op == OpBound {
		if replacement, ok := bindings[t.Name]; ok {
			return replacement
		}
		return t
	}
	if len(t.Args) == 0 {
		return t
	}
	var args []*Term
	for i, arg := range t.Args {
		replaced := Subst(arg, bindings)
		if replaced != arg && args == nil {
			args = append([]*Term(nil), t.Args...)
		}
		if args != nil {
			args[i] = replaced
		}
	}
	if args == nil {
		return t
	}
	return &Term{Op: t.Op, Sort: t.Sort, Name: t.Name, Val: t.Val, Args: args}
}

var infix = map[Op]string{
	OpAdd: " + ", OpMul: " * ", OpDiv: " / ", OpMod: " % ",
	OpEq: " = ", OpLe: " <= ", OpLt: " < ",
	OpAnd: " And ", OpOr: " Or ", OpImplies: " -> ", OpIff: " <-> ",
}

// String renders the term in the annotation syntax, fully parenthesised.
func (t *Term) String() string {
	var b strings.Builder
	t.write(&b)
	return b.String()
}

// write renders one node: leaves and special forms get dedicated syntax, and
// every remaining operator is printed infix between parentheses.
func (t *Term) write(b *strings.Builder) {
	list := func(open string, args []*Term, sep, end string) {
		b.WriteString(open)
		for i, arg := range args {
			if i > 0 {
				b.WriteString(sep)
			}
			arg.write(b)
		}
		b.WriteString(end)
	}
	switch t.Op {
	case OpIntLit:
		b.WriteString(strconv.FormatInt(t.Val, 10))
	case OpTrue:
		b.WriteString("True")
	case OpFalse:
		b.WriteString("False")
	case OpConst, OpBound:
		b.WriteString(t.Name)
	case OpNeg:
		list("-", t.Args, "", "")
	case OpNot:
		list("~", t.Args, "", "")
	case OpLen:
		list("|", t.Args, "", "|")
	case OpSelect:
		t.Args[0].write(b)
		list("[", t.Args[1:], "", "]")
	case OpStore:
		t.Args[0].write(b)
		list("[", t.Args[1:], " := ", "]")
	case OpFill:
		list("fill(", t.Args, ", ", ")")
	case OpPush:
		list("push(", t.Args, ", ", ")")
	case OpIte:
		list("ite(", t.Args, ", ", ")")
	case OpForall:
		list("(Forall ", t.Args, " : ", ")")
	case OpExists:
		list("(Exists ", t.Args, " : ", ")")
	case OpPred:
		list(t.Name+"(", t.Args, ", ", ")")
	default:
		list("(", t.Args, infix[t.Op], ")")
	}
}
