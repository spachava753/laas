package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"math/big"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// == on interface values (S3 of F34).
//
// Go's == on two interface values is true when both are nil, or when both
// hold values of one dynamic type and the values are equal by == of that
// type; it panics when they hold values of one type on which == panics,
// such as a slice, or a struct with a slice or an interface value that
// holds one. Its result is a fresh boolean, with these facts: two nil
// values are equal, a nil value and another are not, two values of
// different dynamic types are not, and two values of one type met in the
// function on which == is identity are equal exactly when what they hold
// is. Nothing else is said, so == of two floats that are NaN is not proved
// either way. Whether it may panic is a table of its own, eqpanics, read
// at a tag, with ground facts for the types the function knows, as
// implements is: an unknown dynamic type may panic.
//
// A value of a concrete type beside an interface value is compared as Go
// does, which converts it: its tag is its type's, and its leaves are
// compared directly. Its type must be one on which == cannot panic, since
// the interface value may hold one.
//
// An error beside another interface value is converted to an interface
// value first, which holds the error.

// eqPanics names the table of the dynamic types on which == panics.
var eqPanics = logic.Const("eqpanics", logic.BoolSeq)

// eqPair is a comparison of two interface values: their references, and
// its result.
type eqPair struct {
	a, b, q *logic.Term
}

// noPanicWhy says why == on two values of type t may panic, or "" when it
// cannot: every part of the value, blank fields included, is comparable
// and no interface value, error, or other value that holds one is part of
// it.
func noPanicWhy(t types.Type, seen map[types.Type]bool) string {
	if seen[t] {
		return ""
	}
	seen[t] = true
	shown := types.TypeString(t, nil)
	switch u := t.Underlying().(type) {
	case *types.Basic:
		if u.Kind() == types.Invalid || u.Info()&types.IsUntyped != 0 && u.Kind() == types.UntypedNil {
			return shown + " is not comparable"
		}
		return ""
	case *types.Pointer, *types.Chan:
		return ""
	case *types.Array:
		return noPanicWhy(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if why := noPanicWhy(field.Type(), seen); why != "" {
				return why
			}
		}
		return ""
	case *types.Interface:
		return "it holds an interface value, " + shown + ", which may hold a value on which == panics"
	}
	return "it is or holds a " + shown + ", on which == panics"
}

// metEqIn reports whether the path of a state has met == on interface
// values.
func metEqIn(st *state) bool {
	return st != nil && st.noted["== met"]
}

// meetEq records that the path of a state compares interface values, and
// states there on which of the types the function knows == panics.
func (v *fnVerifier) meetEq(st *state) {
	if st == nil || metEqIn(st) {
		return
	}
	st.noted["== met"] = true
	for _, t := range v.taggedTypes {
		name, _ := canonicalName(t)
		v.stateEqPanics(st, name, noPanicWhy(t, map[types.Type]bool{}) != "")
	}
	for _, made := range madeErrorTypes {
		// Each is a pointer.
		v.stateEqPanics(st, made, false)
	}
}

// stateEqPanics states once in a state whether == panics on the type of a
// canonical name.
func (v *fnVerifier) stateEqPanics(st *state, typeName string, panics bool) {
	if note := "eqpanics " + typeName; !st.noted[note] {
		st.noted[note] = true
		fact := logic.Select(eqPanics, logic.BigLit(new(big.Int).SetBytes([]byte(typeName))))
		if !panics {
			fact = logic.Not(fact)
		}
		v.fact(st, fact)
	}
}

// eqTypeFact states what == of a pair is when both hold a value of a type
// on which == is identity: whether what they hold is equal.
func (v *fnVerifier) eqTypeFact(st *state, p eqPair, t types.Type) {
	layout, _ := layoutOf(t)
	if !v.identityEq(t) || !capturesValue(layout) {
		return
	}
	name, _ := canonicalName(t)
	tag, _ := typeTag(t)
	var same []*logic.Term
	for i, lf := range layout {
		table := heldTable(name, i, lf)
		same = append(same, eqLeaf(logic.Select(table, p.a), logic.Select(table, p.b)))
	}
	both := logic.And(logic.Ne(p.a, logic.RefLit(0)), logic.Ne(p.b, logic.RefLit(0)), logic.Eq(dynTag(p.a), tag), logic.Eq(dynTag(p.b), tag))
	st.assume(logic.Implies(both, logic.Iff(p.q, logic.And(same...))))
}

// eqSide is one operand of == beside an interface value: the reference of
// an interface value, or a value of a concrete type with its leaves.
type eqSide struct {
	ref      *logic.Term
	concrete types.Type
	leaves   value
}

// compareIfaces evaluates x == y and x != y where one operand is an
// interface value other than an error.
func (v *fnVerifier) compareIfaces(x, y ast.Expr, op token.Token, st *state, guard []*logic.Term, pos token.Pos) *logic.Term {
	tx, ty := v.info.TypeOf(x), v.info.TypeOf(y)
	for _, t := range []types.Type{tx, ty} {
		v.checkEqSide(t, pos)
	}
	vx := v.evalCompared(x, ty, st, guard)
	vy := v.evalCompared(y, tx, st, guard)
	q := v.ifacesEqual(v.eqSide(st, tx, vx), v.eqSide(st, ty, vy), types.ExprString(x), types.ExprString(y), st, guard, pos)
	if op == token.NEQ {
		return logic.Not(q)
	}
	return q
}

// evalCompared evaluates an operand of == beside one of type other. Go
// converts it to other when other is an interface and it is not of that
// type; the value made is only compared, and nothing calls its methods,
// so the operand is evaluated as it is.
func (v *fnVerifier) evalCompared(e ast.Expr, other types.Type, st *state, guard []*logic.Term) value {
	if slices.ContainsFunc(v.findConversions().converted[ast.Unparen(e)], func(t types.Type) bool { return types.Identical(t, other) }) {
		return v.evalConverted(e, other, st, guard)
	}
	return v.eval(e, st, guard)
}

// checkEqSide refuses an operand of a concrete type that == on interface
// values cannot handle: a type with no tag or no model, or one on which ==
// may panic.
func (v *fnVerifier) checkEqSide(t types.Type, pos token.Pos) {
	if types.IsInterface(t) {
		return
	}
	t = types.Default(t)
	shown := types.TypeString(t, types.RelativeTo(v.pass.Pkg))
	if _, named := canonicalName(t); !named {
		v.unsupported(pos, rDynLocalType, fmt.Sprintf("comparing an interface value with a value of type %s is not supported: it is declared inside a function, and nothing tells it apart from another type there", shown))
	}
	if why := heldReason(t); why != "" {
		v.unsupported(pos, rDynCompare, fmt.Sprintf("comparing an interface value with a value of type %s is not supported: %s", shown, why))
	}
	if why := noPanicWhy(t, map[types.Type]bool{}); why != "" {
		v.unsupported(pos, rDynCompare, fmt.Sprintf("comparing an interface value with a value of type %s is not supported: == on two values of %s may panic, since %s", shown, shown, why))
	}
}

// eqSide returns an operand of == as compareIfaces compares it.
func (v *fnVerifier) eqSide(st *state, t types.Type, val value) eqSide {
	switch {
	case isError(t):
		// Go converts the error to the other operand's interface type.
		held := v.fresh("iface", logic.Ref)
		st.assume(logic.Iff(logic.Eq(held, logic.RefLit(0)), logic.IsNil(val[0])))
		v.recordConversion(st, ifaceConversion{ref: held, err: val[0]})
		return eqSide{ref: held}
	case types.IsInterface(t):
		return eqSide{ref: v.named(st, "compared", val[0])}
	}
	t = types.Default(t)
	layout, _ := layoutOf(t)
	return eqSide{concrete: t, leaves: v.goLeaves(st, layout, val)}
}

// ifacesEqual returns Go's == of two operands, one an interface value, and
// proves that it does not panic.
func (v *fnVerifier) ifacesEqual(a, b eqSide, ta, tb string, st *state, guard []*logic.Term, pos token.Pos) *logic.Term {
	if a.ref == nil {
		a, b, ta, tb = b, a, tb, ta
	}
	v.meetDynamic(st)
	v.meetErrorTags(st)
	v.meetEq(st)
	q := v.fresh("equal", logic.Bool)
	aNil := logic.Eq(a.ref, logic.RefLit(0))
	if b.ref == nil {
		t := b.concrete
		v.meetHeldType(st, t)
		tag, _ := typeTag(t)
		st.assume(logic.Implies(aNil, logic.Not(q)))
		st.assume(logic.Implies(logic.And(logic.Not(aNil), logic.Ne(dynTag(a.ref), tag)), logic.Not(q)))
		layout, _ := layoutOf(t)
		if v.identityEq(t) && capturesValue(layout) {
			name, _ := canonicalName(t)
			var same []*logic.Term
			for i, lf := range layout {
				same = append(same, eqLeaf(logic.Select(heldTable(name, i, lf), a.ref), b.leaves[i]))
			}
			st.assume(logic.Implies(logic.And(logic.Not(aNil), logic.Eq(dynTag(a.ref), tag)), logic.Iff(q, logic.And(same...))))
		}
		return q
	}
	bNil := logic.Eq(b.ref, logic.RefLit(0))
	st.assume(logic.Implies(logic.And(aNil, bNil), q))
	st.assume(logic.Implies(logic.Not(logic.Iff(aNil, bNil)), logic.Not(q)))
	st.assume(logic.Implies(logic.And(logic.Not(aNil), logic.Not(bNil), logic.Ne(dynTag(a.ref), dynTag(b.ref))), logic.Not(q)))
	pair := eqPair{a: a.ref, b: b.ref, q: q}
	v.eqPairs = append(v.eqPairs, pair)
	v.sameErrorFacts(st, pair)
	for _, t := range v.metTypes {
		v.eqTypeFact(st, pair, t)
	}
	done := v.at(pos)
	defer done()
	panics := logic.And(logic.Not(aNil), logic.Not(bNil), logic.Eq(dynTag(a.ref), dynTag(b.ref)), logic.Select(eqPanics, dynTag(a.ref)))
	v.check(st, guard, logic.Not(panics), pos, "%s == %s may panic: %s and %s may hold values of one type on which == panics, such as a slice or a struct that holds one; "+
		"say what they hold, as a contract does with holds(%s, T), or assert them first", ta, tb, ta, tb, ta)
	return q
}

// sameErrorFacts states that two interface values made from one error
// that is not nil are equal when the error holds a type on which == is
// identity: a made error, or a typed error of a type met (sameTyped). Of
// another type == may be false of a value and itself, as of a NaN.
func (v *fnVerifier) sameErrorFacts(st *state, p eqPair) {
	for _, ci := range v.ifaceConversions {
		if ci.err == nil {
			continue
		}
		var identity []*logic.Term
		for _, name := range madeErrorTypes {
			identity = append(identity, logic.Eq(errorTag(ci.err), logic.BigLit(new(big.Int).SetBytes([]byte(name)))))
		}
		for _, t := range v.typedTypes {
			tag, _ := typeTag(t)
			identity = append(identity, logic.Eq(errorTag(ci.err), tag))
		}
		for _, cj := range v.ifaceConversions {
			if cj.err == nil || cj.err.String() != ci.err.String() {
				continue
			}
			st.assume(logic.Implies(logic.And(logic.Eq(p.a, ci.ref), logic.Eq(p.b, cj.ref), ci.holds(), cj.holds(), logic.Or(identity...)), p.q))
		}
	}
}
