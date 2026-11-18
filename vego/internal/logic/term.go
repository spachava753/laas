// Package logic defines the first-order specification language used by vego:
// its terms, the parser for annotation clauses, and the resolver that
// turns parsed clauses into typed terms.
package logic

import (
	"math/big"
	"strings"
)

// Sort is the type of a logical term.
type Sort int

// The sorts of the logic. Integers are mathematical (unbounded) integers.
// Float and Err are opaque: a float has no known properties at all, and an
// error has exactly one, whether it is nil. A Ref is the identity of an
// object in memory; the logic treats it as a number, and nil is zero.
//
// A sequence sort is its element sort plus seqStep for each level, so
// sequences nest to any depth: a sequence of integers models a slice or a
// string, and a sequence indexed by Ref models the part of memory that holds
// one field of every object of a type.
const (
	Int Sort = iota
	Bool
	Float
	Err
	Ref
	seqStep

	IntSeq   = Int + seqStep
	BoolSeq  = Bool + seqStep
	FloatSeq = Float + seqStep
)

// IsSeq reports whether the sort is a sequence sort.
func (s Sort) IsSeq() bool { return s >= seqStep }

// Elem returns the element sort of a sequence sort.
func (s Sort) Elem() Sort { return s - seqStep }

// SeqOf returns the sequence sort with the given element sort.
func SeqOf(elem Sort) Sort { return elem + seqStep }

// String returns the Go-flavoured name of the sort.
func (s Sort) String() string {
	if s == IntSeq {
		// A string and a slice of integers are the same to the logic.
		return "string or []int"
	}
	if s.IsSeq() {
		return "[]" + s.Elem().String()
	}
	return [...]string{"int", "bool", "float", "error", "pointer"}[s]
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
	OpConcat // Concat(a, b): the elements of a followed by those of b
	OpSub    // Sub(seq, lo, hi): the elements of seq from lo up to hi
	OpIsNil  // IsNil(err): whether an error value is nil
	OpKey    // Key(seq): a number that identifies a sequence by its contents
	OpPair   // Pair(ref, at): a pointer, which only ever occurs as an operand of RefEq
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
	Name string   // OpConst, OpBound, OpPred
	Val  int64    // OpIntLit
	Big  *big.Int // OpIntLit whose value does not fit Val
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

// BigLit returns an integer literal of any size.
func BigLit(v *big.Int) *Term {
	if v.IsInt64() {
		return IntLit(v.Int64())
	}
	return &Term{Op: OpIntLit, Sort: Int, Big: v}
}

// Value returns the value of an integer literal.
func (t *Term) Value() *big.Int {
	if t.Big != nil {
		return t.Big
	}
	return big.NewInt(t.Val)
}

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

// Concat returns the concatenation of two sequences.
func Concat(a, b *Term) *Term { return node(OpConcat, a.Sort, a, b) }

// Subseq returns the part of seq from index lo up to, not including, hi.
func Subseq(seq, lo, hi *Term) *Term { return node(OpSub, seq.Sort, seq, lo, hi) }

var nilErr = &Term{Op: OpConst, Sort: Err, Name: "nil"}

// RefLit returns the reference with the given number. Number zero is nil.
func RefLit(v int64) *Term { return &Term{Op: OpIntLit, Sort: Ref, Val: v} }

// NilErr returns the nil error.
func NilErr() *Term { return nilErr }

// IsNil returns the formula stating that an error value is nil.
func IsNil(err *Term) *Term {
	if err == nilErr {
		return trueTerm
	}
	return node(OpIsNil, Bool, err)
}

// Pair returns a pointer into an allocation at a position. It is not a term
// the solver knows; RefEq takes it apart. A nil position marks a pointer
// that can be compared with nil but not with another pointer.
func Pair(ref, at *Term) *Term {
	if at == nil {
		return node(OpPair, Ref, ref)
	}
	return node(OpPair, Ref, ref, at)
}

// Incomparable says why two references cannot be compared, or returns ""
// if they can: a pointer with a pointer or with nil, and anything that is
// not a pointer, such as a map, with its like.
func Incomparable(a, b *Term) string {
	isNil := func(t *Term) bool { return t.Op == OpIntLit && t.Val == 0 }
	switch {
	case a.Op != OpPair && b.Op != OpPair:
		return ""
	case a.Op != OpPair || b.Op != OpPair:
		if isNil(a) || isNil(b) {
			return ""
		}
		return "a pointer can only be compared with a pointer or with nil"
	case len(a.Args) != 2 || len(b.Args) != 2:
		return "pointers to values of size zero may or may not be equal, so they can only be compared with nil"
	}
	return ""
}

// RefEq returns the formula stating that two pointers, or a pointer and
// nil, are equal: both nil, or into the same allocation at the same
// position.
func RefEq(a, b *Term) *Term {
	switch {
	case a.Op == OpPair && b.Op == OpPair:
		return And(Eq(a.Args[0], b.Args[0]), Or(Eq(a.Args[0], RefLit(0)), Eq(a.Args[1], b.Args[1])))
	case a.Op == OpPair:
		return Eq(a.Args[0], b)
	case b.Op == OpPair:
		return Eq(a, b.Args[0])
	}
	return Eq(a, b)
}

// Key returns a number that two sequences share exactly when they have the
// same length and the same elements. It lets a string serve as an index.
func Key(seq *Term) *Term { return node(OpKey, Int, seq) }

// SeqEq returns the formula stating that two sequences have the same length
// and the same elements. The bound variable must be fresh.
func SeqEq(a, b, index *Term) *Term {
	inRange := And(Le(IntLit(0), index), Lt(index, Len(a)))
	same := Eq(Select(a, index), Select(b, index))
	return And(Eq(Len(a), Len(b)), Forall(index, Implies(inRange, same)))
}

// Bytes returns the sequence of the bytes of a string.
func Bytes(text string) *Term {
	seq := Fill(IntLit(0), IntLit(0))
	for i := range len(text) {
		seq = Push(seq, IntLit(int64(text[i])))
	}
	return seq
}

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
	return &Term{Op: t.Op, Sort: t.Sort, Name: t.Name, Val: t.Val, Big: t.Big, Args: args}
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
		b.WriteString(t.Value().String())
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
	case OpConcat:
		list("concat(", t.Args, ", ", ")")
	case OpSub:
		list("sub(", t.Args, ", ", ")")
	case OpIsNil:
		list("(", t.Args, "", " = nil)")
	case OpKey:
		list("key(", t.Args, "", ")")
	case OpPair:
		list("pointer(", t.Args, ", ", ")")
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
