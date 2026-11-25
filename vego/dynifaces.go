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

// Assertions to interfaces (S2 of F34).
//
// Whether a dynamic type implements an interface is a table of its own for
// each interface, read at a tag, so that it is a function of the dynamic
// type by construction: implements <canonical name of I>. Nothing writes
// it, and nothing is known of it but ground facts, implements_I[tag(T)] =
// types.Implements(T, I), for each interface met as the target of an
// assertion or a case and each type whose tag the function states: an
// unknown dynamic type may implement anything. The facts are stated once
// both are met, so a function that asserts to no interface asks what it
// asked before.
//
// What the value of such an assertion may be used for:
//
//   - On an operand that is not an error, the value is used only when every
//     method of the target is the very method of the operand's static type,
//     or a method of the same name whose contract the operand's method of the
//     name implies (convertByContract); the assertion is then a conversion
//     that also asks whether the value is nil, and keeps the reference (R2,
//     F2 of the design review). Otherwise a value of the project may be held
//     that has the target's methods but was never checked against them, and
//     code it is handed could call them under no contract; only the forms
//     that discard it are supported.
//   - On an error, the value is used when no method of the target but the
//     very method Error of error has a contract (AC): every method of an
//     error verified code converts is checked to ask nothing and change
//     nothing (checkedMethods), and one of code that is not verified is that
//     code's. It is a new interface value that holds the error.
//   - error as the target of an operand that is not an error is R2's (F1 of
//     the design review).

// implementsTable returns the table that says which dynamic types
// implement an interface, by the interface's canonical name.
func implementsTable(name string) *logic.Term {
	return logic.Const("implements "+name, logic.BoolSeq)
}

// madeErrorMethods lists the methods of the types errors.New and
// fmt.Errorf return, as their packages declare them, which
// TestMadeErrorTypes checks of the running toolchain.
var madeErrorMethods = map[string][]madeMethod{
	`*"errors".errorString`: {{"Error", types.Typ[types.String]}},
	`*"fmt".wrapError`:      {{"Error", types.Typ[types.String]}, {"Unwrap", types.Universe.Lookup("error").Type()}},
	`*"fmt".wrapErrors`:     {{"Error", types.Typ[types.String]}, {"Unwrap", types.NewSlice(types.Universe.Lookup("error").Type())}},
}

// madeMethod is a method without parameters and with one result.
type madeMethod struct {
	name   string
	result types.Type
}

// madeImplements reports whether the made error type of a canonical name
// implements an interface: every method of the interface is one of its
// methods, of the same signature.
func madeImplements(name string, iface *types.Interface) bool {
	methods := madeErrorMethods[name]
	for m := range iface.Methods() {
		i := slices.IndexFunc(methods, func(made madeMethod) bool { return made.name == m.Name() })
		if !m.Exported() || i < 0 {
			return false
		}
		want := types.NewSignatureType(nil, nil, nil, types.NewTuple(), types.NewTuple(types.NewVar(token.NoPos, nil, "", methods[i].result)), false)
		if !types.Identical(m.Type(), want) {
			return false
		}
	}
	return true
}

// noteTagged records a type whose tag the function may state, and states
// whether it implements each interface the path has met as a target. A
// type with no canonical name has no tag, and nothing is stated of it.
func (v *fnVerifier) noteTagged(st *state, t types.Type) {
	name, named := canonicalName(t)
	if !named || types.IsInterface(t) {
		return
	}
	if !slices.ContainsFunc(v.taggedTypes, func(known types.Type) bool { return types.Identical(known, t) }) {
		v.taggedTypes = append(v.taggedTypes, t)
	}
	if st == nil {
		return
	}
	for _, target := range v.ifaceTargets {
		if metIfaceIn(st, target) {
			v.stateImplements(st, name, target, types.Implements(t, target.Underlying().(*types.Interface)))
		}
	}
	if metEqIn(st) {
		v.stateEqPanics(st, name, noPanicWhy(t, map[types.Type]bool{}) != "")
	}
}

// metIfaceIn reports whether the path of a state has met an interface as
// the target of an assertion or a case.
func metIfaceIn(st *state, target types.Type) bool {
	name, _ := canonicalName(target)
	return st != nil && st.noted["iface target "+name]
}

// meetIfaceTarget records that the path of a state meets an interface as
// the target of an assertion or a case, and states there which types the
// function knows implement it: the types whose tags it states, the types
// of made errors, and, for error, the type of every error converted to an
// interface.
func (v *fnVerifier) meetIfaceTarget(st *state, target types.Type) {
	if st == nil || metIfaceIn(st, target) {
		return
	}
	name, _ := canonicalName(target)
	st.noted["iface target "+name] = true
	if !slices.ContainsFunc(v.ifaceTargets, func(known types.Type) bool { return types.Identical(known, target) }) {
		v.ifaceTargets = append(v.ifaceTargets, target)
	}
	iface := target.Underlying().(*types.Interface)
	for _, t := range v.taggedTypes {
		tname, _ := canonicalName(t)
		v.stateImplements(st, tname, target, types.Implements(t, iface))
	}
	for _, made := range madeErrorTypes {
		v.stateImplements(st, made, target, madeImplements(made, iface))
	}
	if isError(target) && dynMetIn(st) {
		for _, c := range v.ifaceConversions {
			if c.err != nil {
				v.errorImplements(st, c)
			}
		}
	}
}

// stateImplements states once in a state whether the type of a canonical
// name implements an interface.
func (v *fnVerifier) stateImplements(st *state, typeName string, target types.Type, implements bool) {
	name, _ := canonicalName(target)
	if note := "implements " + name + " " + typeName; !st.noted[note] {
		st.noted[note] = true
		fact := logic.Select(implementsTable(name), logic.BigLit(new(big.Int).SetBytes([]byte(typeName))))
		if !implements {
			fact = logic.Not(fact)
		}
		v.fact(st, fact)
	}
}

// errorImplements states that an interface value made from an error that
// is not nil holds a type that implements error.
func (v *fnVerifier) errorImplements(st *state, c ifaceConversion) {
	name, _ := canonicalName(types.Universe.Lookup("error").Type())
	v.fact(st, logic.Implies(c.holds(), logic.Select(implementsTable(name), dynTag(c.ref))))
}

// ifaceHolds returns whether an interface value or an error, whose static
// type is from, holds a value that implements an interface: it is not nil,
// and, unless from has every method of the target, its dynamic type
// implements it.
func (v *fnVerifier) ifaceHolds(st *state, x *logic.Term, from, target types.Type) *logic.Term {
	ref, isNil := refOf(x)
	if types.Implements(from, target.Underlying().(*types.Interface)) {
		return logic.Not(isNil)
	}
	v.meetIfaceTarget(st, target)
	name, _ := canonicalName(target)
	return logic.And(logic.Not(isNil), logic.Select(implementsTable(name), dynTag(ref)))
}

// ifaceTargetWhy says why an interface cannot be asserted to at all, or
// "": one with no canonical name, as one declared in a function, which
// nothing tells apart from another.
func ifaceTargetWhy(target types.Type) string {
	if _, named := canonicalName(target); !named {
		return "it is declared inside a function, and nothing tells it apart from another type there"
	}
	return ""
}

// usedIfaceWhy says why the value of an assertion of an operand of static
// type from to an interface cannot be used, or "" when it can; shown
// writes a type, and what names the value in the message.
func (v *fnVerifier) usedIfaceWhy(from, target types.Type, what string, shown func(types.Type) string) string {
	discard := fmt.Sprintf("; write it as _, ok := %s, or as a case of %s whose clause does not use its variable", what, shown(target))
	if !isError(from) {
		iface := target.Underlying().(*types.Interface)
		for m := range iface.Methods() {
			found, _, _ := types.LookupFieldOrMethod(from, false, m.Pkg(), m.Name())
			if _, ok := found.(*types.Func); ok {
				continue
			}
			// Values of an O-typed static type were checked against the
			// interfaces of O its package builds with where they were
			// converted, and those of code that is not verified are
			// assumed to meet them (F35).
			if v.oTyped(from) && v.optionalMember(from, m) != nil {
				continue
			}
			lift := fmt.Sprintf("; the value of an assertion of an interface value may use a method its static type lacks only when the method belongs to an interface whose every method "+
				"has an entry in the trust files, with no states, as io.StringWriter does, and the static type has every method of such an interface, as io.Writer has, "+
				"since values of that type are checked against those interfaces where they are converted; %s is not such a method of %s", m.Name(), shown(from))
			if isIface(from) && !v.oTyped(from) {
				lift = fmt.Sprintf("; the value of an assertion of an interface value may use a method its static type lacks only when the static type has every method of an interface "+
					"whose every method has an entry in the trust files, as io.Writer does, from its declaration or under a contract that implies the entry, since only values of such types "+
					"are checked against the interfaces that code may assert them to; %s has none", shown(from))
				if from.Underlying().(*types.Interface).NumMethods() > 0 {
					lift += ", and an interface whose contracts are in source is not one, since a conversion in one package is not checked against an interface declared in another"
				}
			}
			if isError(target) {
				lift = ""
			}
			return fmt.Sprintf("%s has the method %s, which %s does not have, so the value held may be one verified code made without checking it against %s, "+
				"and code it is handed could call %s under no contract%s%s", shown(target), m.Name(), shown(from), shown(target), m.Name(), lift, discard)
		}
		if why := v.optionalSourceWhy(from, target); why != "" {
			return why + discard
		}
		if isError(target) {
			return fmt.Sprintf("an error made from a value of %s is not followed as an error%s", shown(from), discard)
		}
		return ""
	}
	if v.hasStates(target) || v.stateSpeaker(target) != nil {
		return fmt.Sprintf("%s has methods whose contracts speak of its states or what its value owns, which an error does not keep%s", shown(target), discard)
	}
	errorMethod := types.Universe.Lookup("error").Type().Underlying().(*types.Interface).Method(0)
	for m := range target.Underlying().(*types.Interface).Methods() {
		if m != errorMethod && v.methodContract(m) != nil {
			return fmt.Sprintf("the method %s of %s has a contract, and nothing claims that what the error holds meets it: code that is not verified may have made it%s",
				m.Name(), shown(target), discard)
		}
	}
	return ""
}

// assertedIface returns the value of an assertion to an interface whose
// value is used: on an operand that is not an error, the operand itself,
// converted by contract; on an error, a new interface value that holds the
// error, nil when it does not hold one that implements the target.
func (v *fnVerifier) assertedIface(e ast.Expr, x *logic.Term, from, target types.Type, holds *logic.Term, st *state, guard []*logic.Term) value {
	if !isError(from) {
		v.convertByContract(e, "asserting", from, target, st, guard)
		// A lift, or an O-shaped target, leans on from being O-typed
		// (F14 of the review of S1).
		if v.oShaped(target) || v.oTyped(from) && !types.Implements(from, target.Underlying().(*types.Interface)) {
			v.proveOTyped(e, from, target, st, guard)
		}
		if v.hasStates(from) && !v.hasStates(target) {
			v.keyedFact(st, logic.Implies(logic.Ne(x, logic.RefLit(0)), logic.Select(keyedByHeld, x)))
		}
		return value{x}
	}
	held := v.fresh("asserted iface", logic.Ref)
	st.assume(logic.Iff(logic.Ne(held, logic.RefLit(0)), holds))
	v.recordConversion(st, ifaceConversion{ref: held, err: x, when: holds})
	return value{held}
}

// assertIface evaluates x.(I) for an interface I other than error on an
// error, and for any interface on another interface value.
func (v *fnVerifier) assertIface(e *ast.TypeAssertExpr, st *state, guard []*logic.Term, commaOk bool) []value {
	from, target := v.info.TypeOf(e.X), v.info.TypeOf(e.Type)
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	operand := "an error"
	if !isError(from) {
		operand = "an interface value"
	}
	if why := ifaceTargetWhy(target); why != "" {
		v.unsupported(e.Pos(), fmt.Sprintf("asserting %s to %s is not supported: %s", operand, shown(target), why))
	}
	used := !(commaOk && v.discarded[e])
	if used {
		if why := v.usedIfaceWhy(from, target, types.ExprString(e), shown); why != "" {
			v.unsupported(e.Pos(), fmt.Sprintf("using the value of %s is not supported: %s", types.ExprString(e), why))
		}
	}
	x := v.expr(e.X, st, guard)
	x = v.named(st, "asserted", x)
	if isError(from) {
		v.meetErrorTags(st)
	} else {
		v.meetDynamic(st)
	}
	holds := v.ifaceHolds(st, x, from, target)
	var got value
	if used {
		got = v.assertedIface(e.X, x, from, target, holds, st, guard)
	} else if isError(target) {
		got = value{logic.NilErr()}
	} else {
		got = value{logic.RefLit(0)}
	}
	if !commaOk {
		v.checkAssertion(st, guard, holds, e, types.ExprString(e), fmt.Sprintf("%s may not hold a value that implements %s", types.ExprString(e.X), shown(target)))
		return []value{got}
	}
	return []value{got, {holds}}
}

// meetErrorTags records that the function asks what an error holds, as
// meetAssertion does, for a target that is not a concrete type.
func (v *fnVerifier) meetErrorTags(st *state) {
	v.typedMet = true
	for _, made := range v.distinct {
		v.noteMadeTag(st, made)
	}
}

// ifaceCase returns what a case of an interface type in a type switch
// asks.
func (v *fnVerifier) ifaceCase(e ast.Expr, x *logic.Term, from, t types.Type, st *state) *logic.Term {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	if why := ifaceTargetWhy(t); why != "" {
		v.unsupported(e.Pos(), fmt.Sprintf("a case of %s in a type switch is not supported: %s", shown(t), why))
	}
	if isError(from) {
		v.meetErrorTags(st)
	}
	return v.ifaceHolds(st, x, from, t)
}

// ifaceCaseVar returns the value of the variable of a clause of one
// interface type that the clause uses.
func (v *fnVerifier) ifaceCaseVar(e, operand ast.Expr, x *logic.Term, from, t types.Type, holds *logic.Term, st *state) value {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	what := fmt.Sprintf("%s.(%s)", types.ExprString(operand), shown(t))
	if why := v.usedIfaceWhy(from, t, what, shown); why != "" {
		v.unsupported(e.Pos(), fmt.Sprintf("using the variable of the case %s of the type switch is not supported: %s", shown(t), why))
	}
	return v.assertedIface(operand, x, from, t, holds, st, nil)
}
