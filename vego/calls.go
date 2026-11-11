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
		v.checkAlloc(st, guard, logic.Len(joined), types.Typ[types.Uint8], pos, "the joined string")
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
		v.check(st, guard, v.separate(args[pair[0]], args[pair[1]], pair[0].Type()), call.Pos(),
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
		v.checkWrite(st, guard, t.reach(), call.Pos(), fmt.Sprintf("%s may modify %s", name, what))
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
	// What the types guarantee of everything the call took and produced.
	// The state only holds such facts for the elements that were actually
	// read, and both the check of a trusted promise below and the proof
	// that this call succeeds may need the rest.
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
	// Nobody has proved what a trusted contract promises. If the promise
	// contradicts what is known at this call, everything after the call
	// would be provable, so that is looked for and reported. A state that
	// was contradictory already, given what the types guarantee, belongs to
	// a path that is never taken, and the contract is not to blame for it.
	// Resolving the promise notes more of what the types guarantee, so that
	// is done before the state is looked at for the first time.
	promised := make([]*logic.Term, len(fn.ensures))
	for i, c := range fn.ensures {
		promised[i] = v.calleeFormula(c, post)
	}
	dead := fn.trust == nil || v.quickly(st, involved, logic.False())
	for _, promise := range promised {
		st.assume(logic.Implies(logic.And(guard...), promise))
	}
	if !dead && v.quickly(st, involved, logic.False()) {
		v.report(call.Pos(), "the trusted contract of %s cannot be true of this call: what it promises contradicts what is known here", name)
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
	v.noteFailureSource(fn, results, st, involved)
	return results
}

// receiver evaluates the receiver of a method call as the method takes it.
// A method with a value receiver called on a pointer gets a copy of the
// struct. A method with a pointer receiver called on a struct gets a pointer
// to it: the struct is a variable, one that another pointer points to, an
// element of a slice, or a field of one of these.
func (v *fnVerifier) receiver(call *ast.CallExpr, recv *types.Var, st *state, guard []*logic.Term) value {
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	selection := v.info.Selections[sel]
	if !ok || selection == nil || selection.Kind() != types.MethodVal {
		v.unsupported(call.Pos(), "this method call is not supported")
	}
	if _, ok := layoutOf(recv.Type()); !ok {
		v.unsupported(call.Pos(), fmt.Sprintf("receivers of type %s are not supported", recv.Type()))
	}
	// The operand is followed through the embedded structs the method is
	// promoted from. where is the position of the current struct while it
	// is known to lie in memory.
	// The operand is evaluated once, as Go does: a struct that lies in
	// memory is located, and its value read from there.
	t := v.info.TypeOf(sel.X)
	var cur, where value
	if _, isStruct := t.Underlying().(*types.Struct); isStruct && v.place(sel.X).kind == placeMem {
		lv := v.lvalue(sel.X, st, guard)
		where, cur = value{lv.ref, logic.Add(lv.at, logic.IntLit(lv.offset))}, v.load(lv, st)
	} else {
		cur = v.eval(sel.X, st, guard)
	}
	path := selection.Index()
	for _, index := range path[:len(path)-1] {
		object, viaPointer := pointee(t)
		if viaPointer {
			v.checkNil(st, guard, cur[0], sel.Sel.Pos())
			where = cur
		} else {
			object = t
		}
		next, fieldType, ok := v.member(st, st.mem, cur, t, index)
		if !ok {
			v.unsupported(sel.Sel.Pos(), fmt.Sprintf("this field has type %s, which is not supported", fieldType))
		}
		if where != nil {
			where = value{where[0], logic.Add(where[1], logic.IntLit(v.fieldOffset(object, index)))}
		}
		cur, t = next, fieldType
	}
	_, wantPointer := recv.Type().Underlying().(*types.Pointer)
	object, havePointer := pointee(t)
	switch {
	case wantPointer == havePointer:
		return cur
	case wantPointer && where != nil:
		return where
	case wantPointer:
		v.unsupported(call.Pos(), fmt.Sprintf(
			"calling %s takes the address of %s, which is not supported", sel.Sel.Name, types.ExprString(sel.X)))
	}
	v.checkNil(st, guard, cur[0], sel.Pos())
	return v.pointed(st, object, cur)
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
		target := v.fetch(nil, mem, v.cellsOf(object), val[0], val[1])
		return logic.And(v.wellFormed(target, object, brk), v.contentFacts(mem, target, object, brk, false))
	case *types.Struct:
		var facts []*logic.Term
		for i := range u.NumFields() {
			if lo, hi, ok := fieldLeaves(t, i); ok {
				facts = append(facts, v.contentFacts(mem, val[lo:hi], u.Field(i).Type(), brk, follow))
			}
		}
		return logic.And(facts...)
	case *types.Map:
		// Whatever a map has for a key, present or not, is a complete value
		// of the value type.
		if !mapModelled(t) {
			break
		}
		leaves, _ := layoutOf(u.Elem())
		index := v.bound("k")
		held := make(value, len(leaves))
		for i, lf := range leaves {
			held[i] = logic.Select(v.row(nil, mem, mapOwner(t)+"#val"+lf.path, lf.sort, val[0]), index)
		}
		return logic.Forall(index, v.wellFormed(held, u.Elem(), brk))
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

// noteFailureSource records a call that may make the success of the function
// under verification unpredictable; whether it does is decided once the
// function has been executed, by tieFailures. A call that provably succeeds never
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
		if results[index] == nil {
			continue
		}
		source := (fn.trust != nil && !v.trustForces(fn)) || (fn.imported != nil && fn.imported.Excused)
		if (!local && !source) || solver.Prove(path, logic.IsNil(results[index][0]), opts) == solver.Proved {
			continue
		}
		if v.canReach(path) {
			source := failureSource{err: results[index][0], inLoop: v.looping > 0, known: len(st.chosen), outputs: map[string]bool{}}
			if local {
				source.callee = fn
			}
			for _, result := range results {
				for _, part := range result {
					source.outputs[part.Name] = true
				}
			}
			v.sources = append(v.sources, source)
		}
	}
}

// failureSource is a call whose failure nothing predicts: the error it
// returned, the callee if it is verified in this package, whether the call
// was made inside a loop, the names of everything it returned, and how many
// branches had been taken when it returned.
type failureSource struct {
	err     *logic.Term
	callee  *funcInfo
	inLoop  bool
	outputs map[string]bool
	known   int
}

// estranged returns a term with every constant of the given names replaced
// by a constant nothing is known about, and reports whether there was one.
func estranged(t *logic.Term, names map[string]bool) (*logic.Term, bool) {
	if t.Op == logic.OpConst && names[t.Name] {
		return logic.Const(t.Name+" otherwise", t.Sort), true
	}
	changed := false
	args := make([]*logic.Term, len(t.Args))
	for i, arg := range t.Args {
		replaced, did := estranged(arg, names)
		args[i], changed = replaced, changed || did
	}
	if !changed {
		return t, false
	}
	copied := *t
	copied.Args = args
	return &copied, true
}

// failure is a return of an error that may not be nil, with the conditions
// of the branches taken on the way to it.
type failure struct {
	err  *logic.Term
	path []*logic.Term
	// facts is everything known at the return.
	facts []*logic.Term
}

// tieFailures decides, once the function has been executed, which of the
// calls whose failure nothing predicts make the function itself
// unpredictable: those it fails because of. A call whose error is ignored
// does not excuse a function that then fails for a reason of its own.
//
// The function fails because of a call when the error it returns is the
// call's error, which is proved, so that it also holds for an error that
// was kept in memory in between; or when it returns an error on a path that
// was chosen by what the call returned: the condition of some branch taken
// since the call depends on one of its results. It depends on them when it
// can no longer be proved once they are replaced by values nothing is known
// about; a condition that merely reads memory next to where a result lies
// still can. What a check or a type adds to the state is no such condition. Inside a loop neither can be seen once
// the loop has forgotten the variable that held the error, so an error
// forgotten by a loop counts for the calls made in loops.
func (v *fnVerifier) tieFailures() {
	for _, source := range v.sources {
		tied := slices.ContainsFunc(v.failures, func(f failure) bool {
			opts := solver.Options{Preds: v.res.Preds, MaxSteps: quickSteps}
			if (source.inLoop && v.forgotten[f.err.Name]) || solver.Prove(f.facts, logic.Eq(f.err, source.err), opts) == solver.Proved {
				return true
			}
			return source.known <= len(f.path) && slices.ContainsFunc(f.path[source.known:], func(cond *logic.Term) bool {
				other, mentioned := estranged(cond, source.outputs)
				return mentioned && solver.Prove(f.facts, other, opts) != solver.Proved
			})
		})
		switch {
		case !tied:
		case source.callee != nil:
			v.reached[source.callee] = true
		default:
			v.outside = true
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
	// A trusted function of this package has a body all the same, and what
	// it calls is known.
	from := callee
	if own := v.funcs[callee.obj]; own != nil {
		from = own
	}
	if !v.reaches(from, v.fn) {
		return
	}
	if callee.trust != nil {
		v.report(call.Pos(), "%s is trusted and calls back into %s, so that this call ends cannot be proved; verify %s instead of trusting it",
			callee.obj.Name(), v.fn.obj.Name(), callee.obj.Name())
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
