package vego

import (
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"path/filepath"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// binary builds the term for a binary operator applied to two evaluated
// operands. Division and remainder first have to show a non-zero divisor.
func (v *fnVerifier) binary(op token.Token, x, y *logic.Term, t types.Type, pos token.Pos, st *state, guard []*logic.Term) *logic.Term {
	switch {
	case x.Sort == logic.Err:
		// Two interface values holding the same uncomparable dynamic type,
		// such as a slice type with an Error method, panic when compared.
		v.unsupported(pos, "comparing two errors can panic when they hold an uncomparable type; "+
			"compare with nil, or use errors.Is")
	case x.Sort == logic.Float:
		return v.opaque(op, x)
	case x.Sort == logic.Ref && op == token.EQL:
		return logic.Eq(x, y)
	case x.Sort == logic.Ref && op == token.NEQ:
		return logic.Ne(x, y)
	case x.Sort == logic.Ref || x.Sort == logic.Bool && op != token.EQL && op != token.NEQ:
		v.unsupported(pos, fmt.Sprintf("operator %s is not supported here", op))
	case x.Sort.IsSeq() && op == token.ADD:
		joined := logic.Concat(x, y)
		v.checkFits(st, guard, logic.Len(joined), types.Typ[types.Int], pos, "string length")
		return joined
	case x.Sort.IsSeq() && (op == token.EQL || op == token.NEQ):
		same := logic.SeqEq(x, y, v.bound("k"))
		if op == token.NEQ {
			return logic.Not(same)
		}
		return same
	case x.Sort.IsSeq():
		return v.opaque(op, x)
	}
	switch op {
	case token.ADD, token.SUB, token.MUL:
		result := logic.Add(x, y)
		switch op {
		case token.SUB:
			result = logic.Sub(x, y)
		case token.MUL:
			result = logic.Mul(x, y)
		}
		v.checkFits(st, guard, result, t, pos, operation(op))
		return result
	case token.QUO, token.REM:
		v.check(st, guard, logic.Ne(y, logic.IntLit(0)), pos, "possible division by zero")
		if op == token.REM {
			return logic.Mod(x, y)
		}
		// The only quotient that does not fit is the least value over -1.
		if least, _, ok := v.intRange(t); ok && least.Sign() < 0 {
			wraps := logic.And(logic.Eq(x, logic.BigLit(least)), logic.Eq(y, logic.IntLit(-1)))
			v.check(st, guard, logic.Not(wraps), pos, "division may overflow %s", types.TypeString(t, nil))
		}
		return logic.Div(x, y)
	case token.EQL:
		return logic.Eq(x, y)
	case token.NEQ:
		return logic.Ne(x, y)
	case token.LSS:
		return logic.Lt(x, y)
	case token.LEQ:
		return logic.Le(x, y)
	case token.GTR:
		return logic.Lt(y, x)
	case token.GEQ:
		return logic.Le(y, x)
	}
	v.unsupported(pos, fmt.Sprintf("operator %s is not supported", op))
	return nil
}

// call verifies a call modularly: the callee's precondition must hold, its
// measure must decrease when the call is recursive, what its Modifies
// clauses list is forgotten, and its postcondition is assumed. The callee's
// body is never inspected, so an unannotated callee tells the caller nothing.
func (v *fnVerifier) call(call *ast.CallExpr, st *state, guard []*logic.Term) []value {
	callee, _ := typeutil.Callee(v.info, call).(*types.Func)
	if callee == nil {
		v.unsupported(call.Pos(), "only calls to named functions and methods are supported")
	}
	if errorConstructor(callee) {
		return []value{{v.newError(call, st, guard)}}
	}
	sig := callee.Type().(*types.Signature)
	switch {
	case sig.Variadic() || sig.TypeParams() != nil || sig.RecvTypeParams() != nil:
		v.unsupported(call.Pos(), "calls to variadic and generic functions are not supported yet")
	case sig.Recv() != nil && types.IsInterface(sig.Recv().Type()):
		v.unsupported(call.Pos(), "calls through an interface are not supported yet")
	}
	// Nothing may be called on trust that is not written down: the callee
	// is either verified against its annotations or has a trusted contract.
	fn := v.contractOf(callee)
	if fn == nil {
		v.unsupported(call.Pos(), fmt.Sprintf(
			"it calls %s, which has no contract; annotate %s with //@ so that it is verified, "+
				"or add a trusted contract for %s to %s", callee.Name(), callee.Name(), callee.FullName(), TrustFileName))
	}
	for _, defect := range fn.defects {
		if fn.trust == nil {
			v.report(call.Pos(), "the contract of %s cannot be used: %s", callee.FullName(), defect)
			continue
		}
		v.report(call.Pos(), "the trusted contract of %s (%s:%d) cannot be used: %s",
			fn.trust.key, filepath.Base(fn.trust.file.path), fn.trust.line, defect)
	}
	if fn.broken {
		v.unsupported(call.Pos(), callee.Name()+" has a contract that could not be understood")
	}
	if fn.trust != nil {
		v.noteUse(fn, call.Pos())
	}
	args := map[*types.Var]value{}
	passed := map[*types.Var]string{}
	if sig.Recv() != nil {
		args[sig.Recv()] = v.receiver(call, sig.Recv(), st, guard)
		passed[sig.Recv()] = types.ExprString(ast.Unparen(call.Fun).(*ast.SelectorExpr).X)
	}
	for i, arg := range call.Args {
		passed[sig.Params().At(i)] = types.ExprString(arg)
		param := sig.Params().At(i)
		if _, ok := layoutOf(param.Type()); !ok {
			v.unsupported(arg.Pos(), fmt.Sprintf("arguments of type %s are not supported", param.Type()))
		}
		args[param] = v.evalAs(arg, param.Type(), st, guard)
	}
	name := callee.Name()
	for _, pair := range overlapping(fn) {
		v.check(st, guard, separate(args[pair[0]], args[pair[1]]), call.Pos(),
			"the slices passed to %s as %s and %s may overlap", name, describe(pair[0]), describe(pair[1]))
	}
	// The contract speaks about memory as it is now, before the call.
	before, existed := maps.Clone(st.mem), st.brk
	for _, param := range fn.params {
		if args[param] != nil {
			v.checkInvariants(st, guard, before, args[param], param.Type(), call.Pos(), "what is passed to "+name+" as "+describe(param))
		}
	}
	pre := &specEnv{v: v, sink: st, fn: fn, args: args, now: before}
	for _, c := range fn.requires {
		v.checkClause(c, pre, st, guard, call.Pos(), "precondition of "+name+" may not hold")
	}
	v.checkRecursion(fn, pre, st, guard, call)
	written := v.targets(fn, args, st, before)
	if len(written) > 0 && (call != v.effectful || len(guard) > 0) {
		v.unsupported(call.Pos(), fmt.Sprintf(
			"%s may modify %s, so the call must be a statement of its own "+
				"or the whole right-hand side of an assignment to variables", name, written[0].text))
	}
	for _, t := range written {
		what := "what it calls " + t.text
		if t.param != nil {
			what = passed[t.param]
		}
		v.checkWrite(st, guard, t.owner()+t.prefix, t.ref, t.lo, t.hi, call.Pos(), fmt.Sprintf("%s may modify %s", name, what))
	}
	for _, t := range written {
		v.havoc(st, t)
	}
	// The callee may have created objects.
	st.brk = v.fresh("brk", logic.Ref)
	st.assume(logic.Le(existed, st.brk))
	results := make([]value, sig.Results().Len())
	for i := range results {
		if _, ok := layoutOf(sig.Results().At(i).Type()); ok {
			results[i] = v.unknown(name, sig.Results().At(i).Type(), st)
		}
	}
	post := &specEnv{v: v, sink: st, fn: fn, args: args, results: results, now: before, post: st.mem, before: existed}
	for _, c := range fn.ensures {
		st.assume(logic.Implies(logic.And(guard...), v.calleeFormula(c, post)))
	}
	// A verified function has proved the invariants of what it hands back.
	// A trusted one has proved nothing, so nothing is assumed of it.
	if fn.trust == nil {
		for _, param := range fn.params {
			if args[param] != nil {
				v.assumeInvariants(st, guard, st.mem, args[param], param.Type())
			}
		}
		for i, result := range results {
			if result != nil {
				v.assumeInvariants(st, guard, st.mem, result, sig.Results().At(i).Type())
			}
		}
	}
	// What the types guarantee of everything the call took and produced,
	// which a proof that this call succeeds may need: the state only holds
	// such facts for the elements that were actually read.
	involved := slices.Clip(guard)
	for i, result := range results {
		if result != nil {
			involved = append(involved, v.deepFacts(st.mem, result, sig.Results().At(i).Type(), st.brk))
		}
	}
	for _, param := range fn.params {
		if args[param] != nil {
			involved = append(involved, v.deepFacts(before, args[param], param.Type(), st.brk),
				v.deepFacts(st.mem, args[param], param.Type(), st.brk))
		}
	}
	v.noteFailureSource(fn, results, st, involved)
	return results
}

// receiver evaluates the receiver of a method call as the method takes it.
// A method with a value receiver called on a pointer gets a copy of the
// object; a method with a pointer receiver called on a variable would need
// the variable's address, which is not supported.
func (v *fnVerifier) receiver(call *ast.CallExpr, recv *types.Var, st *state, guard []*logic.Term) value {
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	selection := v.info.Selections[sel]
	if !ok || selection == nil || selection.Kind() != types.MethodVal {
		v.unsupported(call.Pos(), "this method call is not supported")
	}
	if _, ok := layoutOf(recv.Type()); !ok {
		v.unsupported(call.Pos(), fmt.Sprintf("receivers of type %s are not supported", recv.Type()))
	}
	path := selection.Index()
	cur := v.fields(v.eval(sel.X, st, guard), v.info.TypeOf(sel.X), path[:len(path)-1], st, guard, sel.Sel.Pos())
	t := v.info.TypeOf(sel.X)
	for _, index := range path[:len(path)-1] {
		object := t
		if target, ok := pointee(t); ok {
			object = target
		}
		t = object.Underlying().(*types.Struct).Field(index).Type()
	}
	_, wantPointer := recv.Type().Underlying().(*types.Pointer)
	object, havePointer := pointee(t)
	switch {
	case wantPointer == havePointer:
		return cur
	case wantPointer:
		v.unsupported(call.Pos(), fmt.Sprintf(
			"calling %s takes the address of %s, which is not supported; call it on a pointer", sel.Sel.Name, types.ExprString(sel.X)))
	}
	v.checkNil(st, guard, cur[0], sel.Pos())
	return v.object(st, object, cur[0])
}

// deepFacts states what the type of a value guarantees beyond the value
// itself: that the bytes of a string are bytes, that the elements of a slice
// are values of the element type, field by field and down to the bytes of
// their strings, and the same for the fields of the object a pointer refers
// to. It stops at the pointers found there, since what can be reached has
// no end.
func (v *fnVerifier) deepFacts(mem memory, val value, t types.Type, brk *logic.Term) *logic.Term {
	return logic.And(v.wellFormed(val, t, brk), v.contentFacts(mem, val, t, brk, true))
}

// contentFacts states what the types guarantee of what a value contains or
// refers to.
func (v *fnVerifier) contentFacts(mem memory, val value, t types.Type, brk *logic.Term, follow bool) *logic.Term {
	object, isPointer := pointee(t)
	switch u := t.Underlying().(type) {
	case *types.Basic:
		if isString(t) {
			return v.elementFacts(val[0], types.Typ[types.Uint8])
		}
	case *types.Pointer:
		if !isPointer || !follow {
			break
		}
		leaves, _ := layoutOf(object)
		target := make(value, len(leaves))
		for i, lf := range leaves {
			target[i] = v.cell(nil, mem, typeKey(object)+lf.path, lf, val[0])
		}
		return logic.And(v.wellFormed(target, object, brk), v.contentFacts(mem, target, object, brk, false))
	case *types.Struct:
		var facts []*logic.Term
		for i := range u.NumFields() {
			if lo, hi, ok := fieldLeaves(t, i); ok {
				facts = append(facts, v.contentFacts(mem, val[lo:hi], u.Field(i).Type(), brk, follow))
			}
		}
		return logic.And(facts...)
	case *types.Slice:
		// Every element is a complete value of the element type: numbers in
		// range, pointers to something that exists, slices that are slices.
		leaves, ok := layoutOf(u.Elem())
		if !ok {
			break
		}
		index := v.bound("k")
		inRange := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, val[2]))
		element, _ := v.element(nil, mem, val, t, index)
		facts := []*logic.Term{logic.Forall(index, logic.Implies(inRange, v.wellFormed(element, u.Elem(), brk)))}
		for i, lf := range leaves {
			if lf.part == partValue && lf.sort.IsSeq() {
				// The elements hold strings, whose bytes are bytes.
				at := v.bound("k")
				within := logic.And(logic.Le(logic.IntLit(0), at), logic.Lt(at, val[2]))
				text, _ := v.element(nil, mem, val, t, at)
				facts = append(facts, logic.Forall(at, logic.Implies(within, v.elementFacts(text[i], types.Typ[types.Uint8]))))
			}
		}
		return logic.And(facts...)
	}
	return logic.True()
}

// elementFacts states that every element of a sequence is a value of the
// given type.
func (v *fnVerifier) elementFacts(seq *logic.Term, elem types.Type) *logic.Term {
	index := v.bound("k")
	inRange := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, logic.Len(seq)))
	return logic.Forall(index, logic.Implies(inRange, v.typeFact(logic.Select(seq, index), elem)))
}

// noteFailureSource records whether a call makes the success of the function
// under verification unpredictable. A call that provably succeeds never
// does. Otherwise a trusted callee does when it returns an error and its
// contract never forces success; a callee verified in another package says
// in its published contract whether it is excused for that reason; and a
// callee verified in this package is only noted, since whether it is excused
// is decided once every function has been verified. In each case the call
// must be reachable. facts holds the guard of the call and what the types
// guarantee of its outputs.
func (v *fnVerifier) noteFailureSource(fn *funcInfo, results []value, st *state, facts []*logic.Term) {
	path := append(slices.Clip(st.hyps), facts...)
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	local := fn.decl != nil
	for _, index := range errorResults(fn) {
		if results[index] == nil || (!local && v.outside) || (local && v.reached[fn]) {
			continue
		}
		source := (fn.trust != nil && !v.trustForces(fn)) || (fn.imported != nil && fn.imported.Excused)
		if (!local && !source) || solver.Prove(path, logic.IsNil(results[index][0]), opts) == solver.Proved {
			continue
		}
		if v.canReach(path) {
			v.outside = v.outside || !local
			v.reached[fn] = local
		}
	}
}

// calleeFormula resolves a callee's postcondition at a call site. A result of
// an unsupported type has no term, so a clause that mentions it is skipped.
func (v *fnVerifier) calleeFormula(c *clause, env *specEnv) *logic.Term {
	t, err := v.resolverOf(c).Formula(c.node, env)
	switch {
	case errors.Is(err, errNoValue):
		return logic.True()
	case err != nil:
		v.misread(c, err)
	}
	return t
}

// checkRecursion requires a decreasing measure for every call that can lead
// back to the function under verification.
func (v *fnVerifier) checkRecursion(callee *funcInfo, pre *specEnv, st *state, guard []*logic.Term, call *ast.CallExpr) {
	if !v.reaches(callee, v.fn) {
		return
	}
	for _, fn := range []*funcInfo{v.fn, callee} {
		if fn.measure == nil {
			v.report(call.Pos(), "recursive call needs a //@ Measure annotation on %s to prove termination", fn.obj.Name())
			return
		}
	}
	measure := v.intTerm(callee.measure, pre)
	v.check(st, guard, logic.Lt(measure, v.measure), call.Pos(),
		"measure may not decrease in recursive call: %s", callee.measure.text)
}
