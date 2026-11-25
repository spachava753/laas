package vego

import (
	"fmt"
	"go/ast"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// errors.As and errors.AsType (S5 of F33).
//
// errors.As(err, &v) walks the tree of err: at each error it stops when the
// error's type is assignable to the type of v, which it stores in v; else
// it asks the error's As method, if it has one; else it goes on to what its
// Unwrap method returns. errors.AsType[E](err) walks the same tree, and
// stops where err.(E) holds, which is identity of the types. So the two
// differ where a type is assignable to the target without being it, as an
// unnamed struct is to a named one with the same fields (F3 of the design
// review), and each has a table of its own: whether the walk finds one, and
// the value it finds, both read at ErrRef(err), like what an error holds.
// What is known of them is stated as ground facts for each error and target
// type met, like the trees of errors.Is:
//
//   - nil finds nothing;
//   - an error that holds a value of a type met finds it, when the type is
//     assignable to the target (identical, for AsType), and else finds
//     nothing when the type has no As and no Unwrap method;
//   - an error made by errors.New finds nothing, and one fmt.Errorf made
//     with one %w finds what the error it wraps finds, since neither has an
//     As method, and what the second wraps is what its Unwrap returns.
//
// An error of no type met and no known tree finds what the tables say,
// which nothing constrains. errors.As runs the As and Unwrap methods of
// the tree, so its first argument must have a known origin, as that of
// errors.Is must.

// asKind tells errors.As from errors.AsType.
type asKind int

const (
	asAssignable asKind = iota // errors.As
	asIdentical                // errors.AsType
)

// asTables returns the tables of what the walk of one kind finds for a
// target type: whether it finds one, and each leaf of the value it finds.
func asTables(kind asKind, t types.Type) (found *logic.Term, leaves []*logic.Term) {
	name, _ := canonicalName(t)
	prefix := []string{"as ", "astype "}[kind]
	found = logic.Const(prefix+name, logic.BoolSeq)
	layout, _ := layoutOf(t)
	for i, lf := range layout {
		leaves = append(leaves, logic.Const(fmt.Sprintf("%sval %s %d%s", prefix, name, i, lf.path), logic.SeqOf(lf.sort)))
	}
	return found, leaves
}

// asRead returns whether the walk of one kind finds a value of a target
// type in an error, and the value.
func asRead(kind asKind, t types.Type, err *logic.Term) (*logic.Term, value) {
	foundTable, leafTables := asTables(kind, t)
	ref := logic.ErrRef(err)
	val := make(value, len(leafTables))
	for i, table := range leafTables {
		val[i] = logic.Select(table, ref)
	}
	return logic.Select(foundTable, ref), val
}

// asPair is an error and a target type that a walk of errors.As or
// errors.AsType was asked of.
type asPair struct {
	err  *logic.Term
	t    types.Type
	kind asKind
}

// noteAs records that the walk of a kind was asked of an error for a
// target type, and states what is known of it: of the error, of the trees
// below it, and for every type met; types and trees met later state it
// again (meetType, noteTree).
func (v *fnVerifier) noteAs(sink *state, err *logic.Term, t types.Type, kind asKind) {
	if hasBound(err) {
		return
	}
	pair := asPair{err: err, t: t, kind: kind}
	known := false
	for _, other := range v.asPairs {
		known = known || other.kind == kind && types.Identical(other.t, t) && other.err.String() == err.String()
	}
	if !known {
		v.asPairs = append(v.asPairs, pair)
	}
	v.asFacts(sink, pair, map[string]bool{})
}

// asFacts states what is known of one walk, for the trees and the types
// met so far.
func (v *fnVerifier) asFacts(sink *state, p asPair, seen map[string]bool) {
	if sink == nil || seen[p.err.String()] {
		return
	}
	seen[p.err.String()] = true
	state := func(fact *logic.Term) {
		if note := "as " + fact.String(); !sink.noted[note] {
			sink.noted[note] = true
			v.fact(sink, fact)
		}
	}
	found, val := asRead(p.kind, p.t, p.err)
	state(logic.Implies(logic.IsNil(p.err), logic.Not(found)))
	// The types met, the target's own among them.
	for _, t0 := range append([]types.Type{p.t}, v.typedTypes...) {
		tag, named := typeTag(t0)
		if !named {
			continue
		}
		holds := logic.And(logic.Not(logic.IsNil(p.err)), logic.Eq(errorTag(p.err), tag))
		matches := types.Identical(t0, p.t)
		if p.kind == asAssignable {
			matches = types.AssignableTo(t0, p.t)
		}
		methods := types.NewMethodSet(t0)
		switch {
		case matches:
			// Assignable here means of identical underlying types, so the
			// value is the same leaves.
			held := v.heldRead(sink, p.err, t0)
			parts := []*logic.Term{found}
			for i := range val {
				parts = append(parts, eqLeaf(val[i], held[i]))
			}
			state(logic.Implies(holds, logic.And(parts...)))
		case methods.Lookup(nil, "As") == nil && methods.Lookup(nil, "Unwrap") == nil:
			state(logic.Implies(holds, logic.Not(found)))
		}
	}
	// The trees known: a made error has no As method, and what fmt.Errorf
	// wrapped is what its Unwrap returns.
	for _, tree := range v.trees {
		if tree.err.String() != p.err.String() {
			continue
		}
		if tree.wraps == nil {
			state(logic.Not(found))
			continue
		}
		inner, innerVal := asRead(p.kind, p.t, tree.wraps)
		parts := []*logic.Term{logic.Iff(found, logic.And(logic.Not(logic.IsNil(tree.wraps)), inner))}
		for i := range val {
			parts = append(parts, eqLeaf(val[i], innerVal[i]))
		}
		state(logic.And(parts...))
		v.asFacts(sink, asPair{err: tree.wraps, t: p.t, kind: p.kind}, seen)
	}
}

// isAsCall reports whether a callee is errors.As or errors.AsType.
func isAsCall(callee *types.Func) bool {
	_, ok := isErrorsAs(callee)
	return ok
}

// isErrorsAs recognises errors.As and errors.AsType.
func isErrorsAs(callee *types.Func) (asKind, bool) {
	if callee == nil || callee.Pkg() == nil || callee.Pkg().Path() != "errors" {
		return 0, false
	}
	switch callee.Name() {
	case "As":
		return asAssignable, true
	case "AsType":
		return asIdentical, true
	}
	return 0, false
}

// asTarget checks the type a walk is asked for: one that errors.As does not
// panic on, a concrete type that implements error, whose value can be
// copied out of an error, and that the tables can name.
func (v *fnVerifier) asTarget(call *ast.CallExpr, t types.Type, who string) {
	shown := types.TypeString(t, types.RelativeTo(v.pass.Pkg))
	switch {
	case types.IsInterface(t):
		v.unsupported(call.Pos(), fmt.Sprintf("%s with a target of the interface type %s is not supported yet: only a concrete type that implements error can be the target", who, shown))
	case !types.Implements(t, errorType):
		v.unsupported(call.Pos(), fmt.Sprintf("%s panics here: the target has type %s, which is not an interface and does not implement error", who, shown))
	}
	if _, ok := holdsState(t); ok {
		v.unsupported(call.Pos(), fmt.Sprintf("%s copies the value it finds, a value of type %s; hold a pointer to it in the error instead",
			who, holding(t, types.RelativeTo(v.pass.Pkg))))
	}
	if _, named := canonicalName(t); !named {
		v.unsupported(call.Pos(), fmt.Sprintf("%s with a target of %s is not supported: it is declared inside a function, and nothing tells it apart from another type there", who, shown))
	}
	if _, ok := layoutOf(t); !ok {
		v.unsupported(call.Pos(), fmt.Sprintf("%s with a target of %s is not supported: values of its type are not modelled", who, shown))
	}
	if why := reflectHeld(t, "", map[types.Type]bool{}); why != "" {
		v.unsupported(call.Pos(), fmt.Sprintf("%s with a target of %s is not supported: %s", who, shown, why))
	}
}

// errorsAs evaluates errors.As(err, &v), which is supported only in that
// form, for a local variable v: it stores what it finds in v, which is no
// pointer the model has to follow, and returns whether it found one; and
// errors.AsType[E](err), which returns the value and whether it found one.
func (v *fnVerifier) errorsAs(call *ast.CallExpr, kind asKind, st *state, guard []*logic.Term) []value {
	who := []string{"errors.As", "errors.AsType"}[kind]
	var target types.Type
	var into ast.Expr
	if kind == asAssignable {
		addr, ok := ast.Unparen(call.Args[1]).(*ast.UnaryExpr)
		id, isIdent := ast.Expr(nil), false
		if ok {
			id, isIdent = ast.Unparen(addr.X).(*ast.Ident)
		}
		variable, isVar := types.Object(nil), false
		if isIdent {
			variable, isVar = v.info.ObjectOf(id.(*ast.Ident)).(*types.Var)
		}
		if !isVar || variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope() {
			v.unsupported(call.Pos(), "errors.As is supported only as errors.As(err, &v) for a local variable v")
		}
		target, into = variable.Type(), id
	} else {
		sig := v.info.TypeOf(call.Fun).(*types.Signature)
		target = sig.Results().At(0).Type()
	}
	v.asTarget(call, target, who)
	err := call.Args[0]
	if !v.knownError(v.bodyOrigins(), err, -1) {
		v.unsupported(err.Pos(), fmt.Sprintf("%s would run the As and Unwrap methods of %s, an error whose origin is not known; "+
			"only an error made by errors.New or fmt.Errorf, here or in a verified function, one that a contract vouches for, or one that holds a value of a type whose errors have a known origin, "+
			"can be its first argument%s", who, types.ExprString(err), v.originWhy(err)))
	}
	x := v.evalAs(err, types.Universe.Lookup("error").Type(), st, guard)[0]
	v.meetAssertion(st, target)
	v.noteAs(st, x, target, kind)
	found, val := asRead(kind, target, x)
	if kind == asIdentical {
		zero := zeroValue(target)
		got := make(value, len(val))
		for i := range val {
			got[i] = logic.Ite(found, val[i], zero[i])
		}
		return []value{got, {found}}
	}
	// errors.As stores into v only when it finds one.
	lv := v.lvalue(into, st, guard)
	old := v.loadRecorded(lv, st, guard, 0)
	stored := make(value, len(val))
	for i := range val {
		stored[i] = logic.Ite(found, val[i], old[i])
	}
	v.store(lv, stored, st)
	return []value{{found}}
}
