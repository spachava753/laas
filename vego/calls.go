package vego

import (
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
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
			"compare with nil")
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
	case token.SHL, token.SHR:
		return v.shift(op, x, y, t, pos, st, guard)
	case token.AND, token.OR, token.XOR, token.AND_NOT:
		return v.bitwise(op, x, y, t, pos, st)
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
	if lit := v.literalOf(call); lit != nil {
		return v.callLiteral(call, lit, st, guard)
	}
	if isBuiltin(v.info, call, "recover") {
		v.unsupported(call.Pos(), recoverRefused)
	}
	method, viaValue := throughValue(v.info, call)
	switch {
	case viaValue:
		return v.callValue(call, st, guard)
	case method != nil:
		return v.callMethod(call, method, st, guard)
	}
	callee := v.pkgVerifier.calleeAt(call)
	if builtin, ok := typeutil.Callee(v.info, call).(*types.Builtin); ok && callee == nil {
		advice := ""
		if builtin.Name() == "copy" {
			advice = "; write the copy as a loop that assigns each element, or, when the two have the same length, as dst = append(dst[:0], src...)"
		}
		v.unsupported(call.Pos(), fmt.Sprintf("the built-in function %s is not supported yet%s", builtin.Name(), advice))
	}
	if callee == nil {
		v.unsupported(call.Pos(), "only calls to named functions and methods are supported")
	}
	// The receiver and the arguments are evaluated before the call, which
	// is an event in the order Go fixes; see order.go.
	u := v.unit
	operands := u.pushCeiling()
	made := unitCall{name: callee.Name(), pos: call.Pos()}
	var results []value
	switch {
	case errorConstructor(callee):
		results = []value{{v.newError(call, st, guard)}}
		u.reach(operands)
		made.pure = true
	case isErrorsIs(callee):
		results = []value{{v.errorsIs(call, st, guard)}}
		u.reach(operands)
		made.pure = true
	default:
		fn, cut := v.contractFor(call, callee, st, guard)
		if cut {
			// The path has ended here; the results stand for nothing.
			u.reach(operands)
			results = v.nothingKnown(callee, st)
			break
		}
		if fn.calls.len() > 0 {
			// What the call runs may read and write anything the caller may.
			results = v.callHanding(call, fn, st, guard, operands)
			break
		}
		args := v.arguments(call, callee, st, guard)
		u.reach(operands)
		formatted := v.checkFormattedAlloc(st, guard, call, fn, args, v.held)
		v.checkFormatRuns(call, v.formatRuns(call, fn), st, guard)
		made.pure = v.callMemoryFree(fn, callee.Type().(*types.Signature))
		results = v.invoke(call, fn, args, st, guard)
		// What Sprintf returns is what fmt wrote, which is no longer than
		// the bound when the bound counts all of it.
		if formatted != nil && returnsFormatted(callee) {
			st.assume(logic.Implies(logic.And(guard...), logic.Le(logic.Len(results[0][0]), formatted)))
		}
	}
	u.calls = append(u.calls, made)
	u.event()
	return results
}

// signatureMemoryFree reports whether no receiver, parameter, or result of
// a signature refers to memory. A contract over such a signature that
// names no package-level variable whose value refers to memory reads no
// memory and means the same whatever memory holds; see callMemoryFree.
func signatureMemoryFree(sig *types.Signature) bool {
	if sig.Recv() != nil && !memoryFree(sig.Recv().Type()) {
		return false
	}
	for _, tuple := range []*types.Tuple{sig.Params(), sig.Results()} {
		for variable := range tuple.Variables() {
			if !memoryFree(variable.Type()) {
				return false
			}
		}
	}
	return true
}

// contractFor returns the contract a call is checked against, after making
// sure that the callee is one vego can call and that its contract is usable.
//
// A contract that cannot be read in full is reported at the call, and the
// call relies only on what can be; see viewOf. When nothing can be relied
// on, the path ends at the call, under guard.
func (v *fnVerifier) contractFor(call *ast.CallExpr, callee *types.Func, st *state, guard []*logic.Term) (*funcInfo, bool) {
	sig := callee.Type().(*types.Signature)
	switch {
	case sig.Recv() != nil && (sig.RecvTypeParams() != nil || genericReceiver(sig.Recv().Type())):
		v.unsupported(call.Pos(), "calls of methods of generic types are not supported yet")
	case sig.TypeParams() != nil:
		v.unsupported(call.Pos(), "calls to generic functions are not supported yet")
	case sig.Recv() != nil && types.IsInterface(sig.Recv().Type()):
		v.unsupported(call.Pos(), "calls through an interface are not supported yet")
	}
	if made := v.pkgVerifier.instanceOf[callee]; made != nil {
		v.checkGenericCallee(call, callee, made)
	}
	// Nothing may be called on trust that is not written down: the callee
	// is either verified against its annotations or has a trusted contract.
	fn := v.contractOf(callee)
	if fn == nil {
		v.unsupported(call.Pos(), fmt.Sprintf(
			"it calls %s, which has no contract; annotate %s with // @ annotations so that it is verified, "+
				"%s", callee.Name(), callee.Name(), v.addEntryAdvice(callee.FullName())))
	}
	view := v.viewOf(fn)
	v.reportUnusable(call.Pos(), view, v.calleeName(callee))
	if view.cut {
		v.cut(st, guard)
		return view.fn, true
	}
	fn = view.fn
	if fn.trust != nil {
		v.noteUse(fn, call.Pos())
		v.checkHandedOver(call, fn)
		v.checkNotHandable(call, fn)
		// What a parameter under formats is given is checked by the rule
		// for formatting: a value passed as any, or each argument of a
		// pack, on its own; formattedArgs refuses a slice passed with ...,
		// since what its elements hold is not known.
		if fn.formatted != nil {
			for _, arg := range v.formattedArgs(call, fn) {
				v.checkFormattable(arg, fn.obj.Name(), false)
			}
		}
	}
	return fn, false
}

// nothingKnown returns values of the results of a call after which the
// path has ended: values of their types of which nothing else is known.
func (v *fnVerifier) nothingKnown(callee *types.Func, st *state) []value {
	sig := callee.Type().(*types.Signature)
	results := make([]value, sig.Results().Len())
	for i := range results {
		if _, ok := layoutOf(sig.Results().At(i).Type()); ok {
			results[i] = v.unknown("cut", sig.Results().At(i).Type(), st)
		}
	}
	return results
}

// calleeName names a function in a message: by its name in this package,
// and in full in another.
func (v *fnVerifier) calleeName(callee *types.Func) string {
	if callee.Pkg() == v.pass.Pkg {
		return callee.Name()
	}
	return callee.FullName()
}

// checkNotHandable refuses a function literal, a function, or a method
// value written as the argument of a trusted function's parameter that its
// entry lists under runs and gives no contract under calls, and whose type
// has no contract. Made into a value of that type it would need a contract
// the type does not have; the entry is where to give one.
func (v *fnVerifier) checkNotHandable(call *ast.CallExpr, fn *funcInfo) {
	for _, passed := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		param, arg := passed.param, passed.expr
		// A parameter whose type has a contract takes a value made of the
		// type, which is checked where it is made. A variadic parameter is
		// a slice, which is no function.
		if passed.packed || (!fn.runs.get(param) && fn.keeps.get(param) == nil) || fn.calls.get(param) != nil || !isFunc(param.Type()) || v.valueContract(param.Type()) != nil {
			continue
		}
		what := types.ExprString(arg)
		switch inner := ast.Unparen(arg).(type) {
		case *ast.FuncLit:
			what = "the function literal"
		default:
			if named, method := v.valueForm(inner); named == nil && method == nil {
				continue
			}
		}
		if !fn.runs.get(param) {
			// What a function keeps runs after the call, which a contract
			// under calls cannot describe.
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is handed to %s as %s, which its trusted contract lists under keeps, and whose type %s has no contract; "+
				"declare a named function type with a contract and pass a value of it", what, fn.obj.Name(), param.Name(), param.Type()))
		}
		v.unsupported(arg.Pos(), fmt.Sprintf("%s is handed to %s as %s, which its trusted contract lists under runs with no contract under calls; "+
			"give %s a contract under calls in the entry for %s", what, fn.obj.Name(), param.Name(), param.Name(), fn.trust.key))
	}
}

// checkHandedOver looks at what a call gives to a trusted function. Such a
// function is believed to write nothing but what its contract lists, and
// its author can vouch for that only as far as its own code goes. An error,
// or anything else that carries code chosen elsewhere, would let it run
// methods nobody has seen, which could write memory the caller reasons
// about. So such a value is passed only to a parameter that the contract
// lists under runs, which says in the open that the contract is claimed to
// hold whatever code arrives there. An error whose origin is known needs no
// such claim, as for formatting: its methods are those of the standard
// library.
func (v *fnVerifier) checkHandedOver(call *ast.CallExpr, fn *funcInfo) {
	sig := fn.obj.Type().(*types.Signature)
	type passed struct {
		param *types.Var
		arg   ast.Expr
		// t is the type the argument is passed as: the parameter's, or the
		// element type of the new slice of a pack.
		t types.Type
	}
	var handed []passed
	if sig.Recv() != nil {
		// A method expression, T.Method(x), takes its receiver as an
		// argument; only a call on a value is supported.
		selector, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
		if selection := v.info.Selections[selector]; !ok || selection == nil || selection.Kind() != types.MethodVal {
			v.unsupported(call.Pos(), "this method call is not supported")
		}
		handed = append(handed, passed{sig.Recv(), selector.X, sig.Recv().Type()})
	}
	for _, bound := range v.bindCall(call, sig) {
		if !bound.packed {
			handed = append(handed, passed{bound.param, bound.expr, bound.param.Type()})
			continue
		}
		// Each argument of a pack is an element of a new slice that
		// holds nothing else.
		for _, arg := range bound.pack {
			handed = append(handed, passed{bound.param, arg, elemType(bound.param.Type())})
		}
	}
	for _, h := range handed {
		param, arg, t := h.param, h.arg, h.t
		// What runs claims for a value whose type has a contract holds
		// only for values that meet it, so the proof rests on the entries
		// that give the types it can hold contracts.
		if fn.runs.get(param) || fn.keeps.get(param) != nil {
			v.noteEntriesIn(param.Type(), arg.Pos())
		}
		// What a parameter under formats is given is checked by the rule
		// for formatting; see checkFormatted.
		if fn.runs.get(param) || fn.keeps.get(param) != nil || (param == fn.formatted && param != nil) || !holdsCode(t, map[types.Type]bool{}) {
			continue
		}
		// Known origin of either kind makes every method harmless.
		if isError(t) && v.knownError(v.bodyOrigins(), arg, -1) {
			continue
		}
		what := "an error whose origin is not known" + v.originWhy(arg)
		if !isError(t) {
			what = fmt.Sprintf("a value of type %s, which is or holds %s", t, heldCode(t, map[types.Type]bool{}))
		}
		v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to %s, which is trusted, and is %s; "+
			"%s could run code through it that nobody has seen. If its contract holds whatever that code does, "+
			"list %s under runs in the contract if %s runs it only while the call lasts, or under keeps, with where it keeps it, "+
			"if it keeps it in a result or a parameter for later calls", types.ExprString(arg), fn.obj.Name(), what, fn.obj.Name(), param.Name(), fn.obj.Name()))
	}
}

// heldAs returns, for the two types of the standard library whose fields
// say less of what they can hold than their package does, the type that
// says it, and replaced = true; every rule that asks whether a value can
// hold code walks that type instead. Its field of type unsafe.Pointer
// would otherwise count as anything at all.
//
//   - sync/atomic.Pointer[T] holds a *T: its one field v is unexported, and
//     package sync/atomic only loads, stores, swaps, and compares it as a
//     *T, so anything else in it needs unsafe, which code that is not
//     verified is assumed not to use to give memory another type.
//   - runtime.Pinner holds the pointers it pins, which nothing reads as
//     values or calls, so it holds nothing: held is nil.
//
// The types are matched by the path of their package and their name, not
// by their shape. sync/atomic.Value and the other types of sync/atomic are
// walked as they are declared.
func heldAs(t types.Type) (held types.Type, replaced bool) {
	named, ok := types.Unalias(t).(*types.Named)
	if !ok || named.Obj().Pkg() == nil {
		return nil, false
	}
	switch path, name := named.Obj().Pkg().Path(), named.Obj().Name(); {
	case path == "sync/atomic" && name == "Pointer" && named.TypeArgs().Len() == 1:
		return types.NewPointer(named.TypeArgs().At(0)), true
	case path == "runtime" && name == "Pinner":
		return nil, true
	}
	return nil, false
}

// heldCode names what a value of a type that holdsCode accepts can hold
// that carries code, the first that holdsCode finds.
func heldCode(t types.Type, seen map[types.Type]bool) string {
	if t == nil || seen[t] {
		return ""
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return heldCode(held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Interface:
		if isError(t) {
			return "an error"
		}
		return "an interface value"
	case *types.Signature:
		return "a function value"
	case *types.Chan:
		return "a channel"
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return "an unsafe.Pointer"
		}
	case *types.Pointer:
		return heldCode(u.Elem(), seen)
	case *types.Slice:
		return heldCode(u.Elem(), seen)
	case *types.Array:
		return heldCode(u.Elem(), seen)
	case *types.Map:
		if what := heldCode(u.Key(), seen); what != "" {
			return what
		}
		return heldCode(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if what := heldCode(field.Type(), seen); what != "" {
				return what
			}
		}
	}
	return ""
}

// holdsCode reports whether a value of a type can hold, however deep, a
// value whose methods or body are chosen where the value is made: an
// interface, a function, a channel through which one may arrive, or an
// unsafe.Pointer, which may point to any of these.
func holdsCode(t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return holdsCode(held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Interface, *types.Signature, *types.Chan:
		return true
	case *types.Basic:
		return u.Kind() == types.UnsafePointer
	case *types.Pointer:
		return holdsCode(u.Elem(), seen)
	case *types.Slice:
		return holdsCode(u.Elem(), seen)
	case *types.Array:
		return holdsCode(u.Elem(), seen)
	case *types.Map:
		return holdsCode(u.Key(), seen) || holdsCode(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if holdsCode(field.Type(), seen) {
				return true
			}
		}
	}
	return false
}

// arguments evaluates the receiver and the arguments of a call, in the
// state in which the call is written.
func (v *fnVerifier) arguments(call *ast.CallExpr, callee *types.Func, st *state, guard []*logic.Term) map[*types.Var]value {
	sig := callee.Type().(*types.Signature)
	args := map[*types.Var]value{}
	if sig.Recv() != nil {
		args[sig.Recv()] = v.receiver(call, sig.Recv(), st, guard)
	}
	for _, passed := range v.bindCall(call, sig) {
		args[passed.param] = v.evalPassed(passed, st, guard)
	}
	return args
}

// invoke applies the contract of a callee to arguments that have been
// evaluated: at the call itself, or earlier for a deferred call, which runs
// when the function returns with the arguments it was given at the defer
// statement.
//
// What it reads of memory is what the contract says, which is not a read Go
// makes; the receiver and the arguments have been read already.
func (v *fnVerifier) invoke(call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value, st *state, guard []*logic.Term) []value {
	var results []value
	v.quietly(func() { results = v.apply(call, fn, args, st, guard) })
	return results
}

// apply does the work of invoke.
func (v *fnVerifier) apply(call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value, st *state, guard []*logic.Term) []value {
	callee := fn.obj
	sig := callee.Type().(*types.Signature)
	passed := map[*types.Var]string{}
	passedExpr := map[*types.Var]ast.Expr{}
	if sig.Recv() != nil {
		passed[sig.Recv()] = types.ExprString(ast.Unparen(call.Fun).(*ast.SelectorExpr).X)
		passedExpr[sig.Recv()] = ast.Unparen(call.Fun).(*ast.SelectorExpr).X
	}
	if fn.receiver != nil {
		passed[fn.receiver] = types.ExprString(ast.Unparen(call.Fun).(*ast.SelectorExpr).X)
	}
	// A call made up to check a function used as a value has no
	// arguments of its own, and its parameters are named as they are.
	bound, _ := bindArgs(v.info, call, paramsOf(sig), sig.Variadic())
	for _, b := range bound {
		passed[b.param] = b.text()
		if !b.packed {
			passedExpr[b.param] = b.expr
		}
	}
	// A call through a function value or an interface value is named as
	// it is written.
	name := callee.Name()
	if fn.valueOf != nil || fn.methodOf != nil {
		name = types.ExprString(call.Fun)
	}
	for _, pair := range overlapping(fn) {
		v.check(st, guard, v.separate(args[pair[0]], args[pair[1]], pair[0].Type()), call.Pos(),
			"the slices passed to %s as %s and %s may overlap", name, describe(pair[0]), describe(pair[1]))
	}
	for _, pair := range v.sharing(fn) {
		if args[pair[0]] != nil && args[pair[1]] != nil {
			v.check(st, guard, apartHomes(args[pair[0]][0], args[pair[1]][0]), call.Pos(),
				"the interface values passed to %s as %s and %s may share their states: they may be one value, hold one value, or hold a value "+
					"and one that wraps it, and %s may rely on them not doing so", name, describe(pair[0]), describe(pair[1]), name)
		}
	}
	// The contract speaks about memory as it is now, before the call.
	before, existed := maps.Clone(st.mem), st.brk
	// Every constant made from here on stands for something the call
	// produced: a result, or memory it may have written.
	mark, known := len(v.made), len(st.hyps)
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
	for i, t := range written {
		what := "what it calls " + t.text
		if t.param != nil {
			what = passed[t.param]
		}
		if t.row {
			what = "the states of " + what
		}
		// What a method writes behind the receiver of a value it is made
		// into is something no clause of that contract can list.
		remedy := ""
		if v.heldReceiver != nil && fn.paramNames[fn.modifies[i].name] == v.heldReceiver {
			remedy = v.heldRemedy
		}
		unlisted := ""
		if t.param != nil && passedExpr[t.param] != nil {
			unlisted = v.notListable(passedExpr[t.param], call.Pos())
		}
		v.checkWriteOr(st, guard, t.reach(), call.Pos(), fmt.Sprintf("%s may modify %s", name, what), remedy, unlisted)
	}
	// What a call that runs what it is handed is like at its start, before
	// anything it writes is forgotten.
	var atCall *state
	if fn.calls.len() > 0 {
		atCall = st.clone()
	}
	for _, t := range written {
		v.havoc(st, t, guard)
	}
	var applied map[*types.Var]*logic.Term
	if fn.calls.len() > 0 {
		applied = v.runHanded(call, fn, args, written, atCall, st, mark)
	}
	if u := v.unit; len(written) > 0 && u != nil {
		u.wrote(st, "the call to "+name)
	}
	// The callee may have created objects, if it ran.
	st.brk = v.fresh("brk", logic.Ref)
	st.assume(logic.Le(existed, st.brk))
	if len(guard) > 0 {
		st.assume(logic.Implies(logic.Not(logic.And(guard...)), logic.Eq(st.brk, existed)))
	}
	results := make([]value, sig.Results().Len())
	for i := range results {
		if _, ok := layoutOf(sig.Results().At(i).Type()); ok {
			results[i] = v.unknown(name, sig.Results().At(i).Type(), st)
			// A write through what a trusted function returned that the
			// caller may not make is reported with the function's name.
			_, isPointer := pointee(sig.Results().At(i).Type())
			if isSlice(sig.Results().At(i).Type()) || isPointer {
				for _, leaf := range results[i] {
					if leaf.Sort == logic.Ref && leaf.Op == logic.OpConst {
						from := returned{fn: fn, result: i, call: name}
						from.param, from.within, from.unlessNew = withinArgument(fn, i, bound)
						v.returnedBy[leaf.Name] = from
					}
				}
			}
		}
	}
	post := &specEnv{v: v, sink: st, fn: fn, args: args, results: results, now: before, post: st.mem, before: existed, applied: applied}
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
	dead := (fn.trust == nil && fn.valueOf == nil && fn.methodOf == nil) || v.quickly(st, involved, logic.False())
	for _, promise := range promised {
		st.assume(logic.Implies(logic.And(guard...), promise))
	}
	if !dead && v.quickly(st, involved, logic.False()) {
		what := "trusted contract of " + name
		switch {
		case fn.valueOf != nil:
			what = "contract of " + fn.obj.Name()
		case fn.methodOf != nil:
			what = "contract of " + methodTitle(fn.methodOf)
		}
		v.report(call.Pos(), "the %s cannot be true of this call: what it promises contradicts what is known here", what)
	}
	// A verified function has proved the invariants of what it hands back.
	// A trusted one has proved nothing, so nothing is assumed of it, and
	// neither is anything of a function value or an interface value,
	// which may come from code that is not verified.
	if fn.trust == nil && fn.valueOf == nil && fn.methodOf == nil {
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
	// What this call produced depends on whatever it was given; that is
	// recorded for tieFailures.
	handed := forward{produced: slices.Clip(v.made[mark:]), facts: slices.Clip(st.hyps[known:])}
	for _, taken := range st.chosen {
		handed.path = append(handed.path, taken.cond)
	}
	for _, param := range fn.params {
		handed.given = append(handed.given, args[param]...)
	}
	v.forwards = append(v.forwards, handed)
	v.noteFailureSource(fn, results, st, involved, handed)
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
	// memory is located, and its value read from there only when the method
	// needs it. A pointer receiver takes its address and reads nothing.
	t := v.info.TypeOf(sel.X)
	path := selection.Index()
	_, wantPointer := recv.Type().Underlying().(*types.Pointer)
	start, what := v.unit.start(), "the receiver of "+types.ExprString(sel)
	if _, isStruct := t.Underlying().(*types.Struct); isStruct && v.place(sel.X).kind == placeMem {
		// The struct is followed by its position, and only the embedded
		// pointers on the way are read.
		lv := v.lvalue(sel.X, st, guard)
		where := value{lv.ref, logic.Add(lv.at, logic.IntLit(lv.offset))}
		for _, index := range path[:len(path)-1] {
			field := t.Underlying().(*types.Struct).Field(index).Type()
			object, isPointer := pointee(field)
			if !isPointer {
				where = value{where[0], logic.Add(where[1], logic.IntLit(v.fieldOffset(t, index)))}
				t = field
				continue
			}
			if _, _, ok := fieldLeaves(t, index); !ok {
				v.unsupported(sel.Sel.Pos(), fmt.Sprintf("this field has type %s, which is not supported", field))
			}
			from, at := types.NewPointer(t), where
			where = v.readAt(st, guard, start, what, sel.Sel.Pos(), func(sink *state, mem memory) value {
				read, _, _ := v.member(sink, mem, at, from, index)
				return read
			})
			v.checkNil(st, guard, where[0], sel.Sel.Pos())
			t = object
		}
		if wantPointer {
			return where
		}
		return v.readAt(st, guard, start, what, sel.Pos(), func(sink *state, mem memory) value {
			return v.pointedIn(sink, mem, t, where)
		})
	}
	var where value
	cur := v.eval(sel.X, st, guard)
	for _, index := range path[:len(path)-1] {
		object, viaPointer := pointee(t)
		if viaPointer {
			v.checkNil(st, guard, cur[0], sel.Sel.Pos())
			where = cur
		} else {
			object = t
		}
		fieldType := object.Underlying().(*types.Struct).Field(index).Type()
		if _, _, ok := fieldLeaves(object, index); !ok {
			v.unsupported(sel.Sel.Pos(), fmt.Sprintf("this field has type %s, which is not supported", fieldType))
		}
		from, pointer := t, cur
		var next value
		if viaPointer {
			next = v.readAt(st, guard, start, what, sel.Sel.Pos(), func(sink *state, mem memory) value {
				read, _, _ := v.member(sink, mem, pointer, from, index)
				return read
			})
		} else {
			// A field of a struct value is part of the value, not memory.
			next, _, _ = v.member(nil, nil, cur, t, index)
		}
		if where != nil {
			where = value{where[0], logic.Add(where[1], logic.IntLit(v.fieldOffset(object, index)))}
		}
		cur, t = next, fieldType
	}
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
	return v.readAt(st, guard, start, what, sel.Pos(), func(sink *state, mem memory) value {
		return v.pointedIn(sink, mem, object, cur)
	})
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
// guarantee of its outputs, and made what the call produced: its results
// and the memory it may have written.
func (v *fnVerifier) noteFailureSource(fn *funcInfo, results []value, st *state, facts []*logic.Term, made forward) {
	defer v.asking(failureCheck)()
	if !v.tracksFailure {
		// Nothing reads the sources of a function that returns no error,
		// or of code that is checked for some other purpose. Whether a
		// trusted contract forces success is still settled, for the
		// trust report.
		if fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
			for _, index := range errorResults(fn) {
				if results[index] != nil {
					v.trustForces(fn)
				}
			}
		}
		return
	}
	path := append(slices.Clip(st.hyps), facts...)
	local := fn.decl != nil
	for _, index := range errorResults(fn) {
		if results[index] == nil {
			continue
		}
		source := ((fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil) && !v.trustForces(fn)) || (fn.imported != nil && fn.imported.Excused)
		if (!local && !source) || v.proves(path, logic.IsNil(results[index][0]), 0) {
			continue
		}
		if v.canReach(path) {
			source := failureSource{outputs: map[string]bool{}}
			if local {
				source.callee = fn
			}
			for _, name := range made.produced {
				source.outputs[name] = true
			}
			source.origins = []forward{made}
			v.sources = append(v.sources, source)
		}
	}
	// What a trusted function returns is just as unpredictable when it is
	// not an error: nothing but its contract says what comes back. A
	// function whose success hangs on that cannot promise success either.
	// Where the contract does determine the results, nothing will be found
	// to depend on them.
	if (fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil) && len(errorResults(fn)) == 0 && len(made.produced) > 0 && v.canReach(path) {
		source := failureSource{outputs: map[string]bool{}, origins: []forward{made}}
		for _, name := range made.produced {
			source.outputs[name] = true
		}
		v.sources = append(v.sources, source)
	}
}

// failureSource is a call whose outcome nothing predicts: the callee if it
// is verified in this package, and the names of everything it produced.
type failureSource struct {
	callee *funcInfo
	// outputs names what the call produced, and whatever tieFailures finds
	// to depend on that: what later calls produced that were given any of
	// it, and the unknowns loops put in place of variables that held it.
	outputs map[string]bool
	// origins holds the calls that produced the outputs.
	origins []forward
}

// otherwise states of other values, named by estranged, what is known of
// the outputs: that they are something the calls could have produced. That
// is what each call added to the state, which is what the types and its
// contract guarantee, and for the unknowns of a loop what holds at its
// head: their types and the invariants. A later call was made on some path, and with another
// outcome of the first call execution might not have come that way, so what
// a call guarantees is stated on condition of the branches that led to it,
// with the outputs replaced in those too.
func (source *failureSource) otherwise() []*logic.Term {
	var facts []*logic.Term
	for _, call := range source.origins {
		reached := make([]*logic.Term, len(call.path))
		for i, cond := range call.path {
			reached[i], _ = estranged(cond, source.outputs)
		}
		for _, fact := range call.facts {
			if other, mentioned := estranged(fact, source.outputs); mentioned {
				facts = append(facts, logic.Implies(logic.And(reached...), other))
			}
		}
	}
	return facts
}

// forward is a call as tieFailures needs it: what the call was given, the
// names of what it produced, the facts it added, and the conditions of the
// branches taken on the way to it.
type forward struct {
	given    []*logic.Term
	produced []string
	facts    []*logic.Term
	path     []*logic.Term
}

// estranged returns a term with every constant of the given names replaced
// by another constant, and reports whether there was one.
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
	return logic.WithArgs(t, args), true
}

// failure is a return, with the errors it returns and the conditions of the
// branches taken on the way to it. It serves for a return that may succeed
// as well as for one that may fail.
type failure struct {
	errs []*logic.Term
	path []choice
	// facts is everything known at the return.
	facts []*logic.Term
}

// tieFailures decides, once the function has been executed, which of the
// calls whose failure nothing predicts make the function itself
// unpredictable: those it fails because of. A call whose error is ignored
// does not excuse a function that then fails for a reason of its own.
//
// A call makes the function unpredictable when it decides between failure
// and success: some return of an error that may not be nil, and some return
// of one that may be nil, each depend on what the call produced, or on what
// a later call that was given any of that produced. A function that fails
// whatever the call does has nothing to be excused for. A return depends on
// the call in one of two ways: whether the error it returns is nil does, or
// the condition of a branch taken on the way to it does. A branch that was
// certain to be taken is not looked at.
//
// Something depends on the results when it cannot be proved to stay as it
// is once they are replaced by other values the call could have returned.
// A read of memory next to where a result lies stays as it is; so does
// anything every value of the result's type satisfies. What a later call
// reads of the results out of memory is not followed, and a function that
// depends on the call only in that way is not excused.
//
// A loop forgets the variables it assigns. The end of the body is where it
// is seen what an iteration leaves in such a variable; if that depends on a
// call, the unknown that stands for the variable afterwards does too. What
// a loop forgets of memory is not followed in this way.
func (v *fnVerifier) tieFailures() {
	defer v.asking(failureCheck)()
	if !v.tracksFailure {
		return
	}
	// What a call produced spreads: to the unknown that stands for a
	// variable a loop forgot, if what an iteration leaves in the variable
	// depends on it, and to what a later call produced, if that call was
	// given any of it. Each can enable the other, and loops are not
	// executed in the order they run, so this is repeated until nothing is
	// added.
	for i := range v.sources {
		source := &v.sources[i]
		summarised := map[*forward]bool{}
		for changed := true; changed; {
			changed = false
			for _, l := range v.left {
				// What the iteration leaves depends on the call if the
				// value does, or if the variable was given a value on a
				// way through the body that the call chose.
				depends := v.dependsOn(source, l.facts, l.val) || (l.val.Name != l.name && v.chosenBy(source, l.facts, l.path))
				if !source.outputs[l.name] && depends {
					source.outputs[l.name], changed = true, true
					if !summarised[l.loop] {
						summarised[l.loop] = true
						source.origins = append(source.origins, *l.loop)
					}
				}
			}
			for _, call := range v.forwards {
				fed := slices.ContainsFunc(call.given, func(part *logic.Term) bool {
					_, mentioned := estranged(part, source.outputs)
					return mentioned
				})
				if fed && len(call.produced) > 0 && !source.outputs[call.produced[0]] {
					for _, name := range call.produced {
						source.outputs[name] = true
					}
					source.origins, changed = append(source.origins, call), true
				}
			}
		}
	}
	for index := range v.sources {
		source := &v.sources[index]
		// The call must make the difference: some return of an error and
		// some return without one both depend on it.
		decides := func(outcome failure) bool {
			return v.chosenBy(source, outcome.facts, outcome.path) ||
				slices.ContainsFunc(outcome.errs, func(err *logic.Term) bool { return v.dependsOn(source, outcome.facts, err) })
		}
		// Each must also be an outcome that some input reaches, the
		// failure with an error that is one and the success with none;
		// that the solver could not rule it out is not enough.
		reached := func(outcome failure, succeeds bool) bool {
			none := make([]*logic.Term, len(outcome.errs))
			for i, err := range outcome.errs {
				none[i] = logic.IsNil(err)
			}
			how := logic.And(none...)
			if !succeeds {
				how = logic.Not(how)
			}
			return decides(outcome) && v.canReach(append(slices.Clone(outcome.facts), how))
		}
		tied := slices.ContainsFunc(v.failures, func(outcome failure) bool { return reached(outcome, false) }) &&
			slices.ContainsFunc(v.successes, func(outcome failure) bool { return reached(outcome, true) })
		switch {
		case !tied:
		case source.callee != nil:
			v.reached[source.callee] = true
		default:
			v.outside = true
		}
	}
}

// dependsOn reports whether a value depends on what a call produced: it
// mentions some of it, and cannot be proved, from the facts given, to stay
// as it is when all of it is replaced by other values the call could have
// produced. Of an error only whether it is nil is compared.
func (v *fnVerifier) dependsOn(source *failureSource, facts []*logic.Term, val *logic.Term) bool {
	if val.Sort == logic.Err {
		val = logic.IsNil(val)
	}
	other, mentioned := estranged(val, source.outputs)
	if !mentioned {
		return false
	}
	stays := v.same(val, other)
	if val.Sort == logic.Bool {
		stays = logic.Iff(val, other)
	}
	return !v.proves(slices.Concat(facts, source.otherwise()), stays, quickEffort)
}

// chosenBy reports whether one of the branches taken was chosen by what a
// call produced: it was not certain to be taken, given the facts known
// before it, and its condition depends on what the call produced.
func (v *fnVerifier) chosenBy(source *failureSource, facts []*logic.Term, path []choice) bool {
	return slices.ContainsFunc(path, func(taken choice) bool {
		return !v.proves(facts[:taken.before], taken.cond, quickEffort) && v.dependsOn(source, facts, taken.cond)
	})
}

// forgottenPart is one part of the value of a variable that a loop made
// unknown: the variable, and which part.
type forgottenPart struct {
	variable *types.Var
	index    int
}

// leftover is what an iteration of a loop left in a variable that the loop
// forgot, for one part of its value: the name of the unknown that stands
// for that part at the head and after the loop, the part at the end of the
// body, and what was known there.
type leftover struct {
	name  string
	val   *logic.Term
	facts []*logic.Term
	// loop says what is known of the unknowns of the loop at its head.
	loop *forward
	// path holds the branches taken in the body on the way to its end.
	path []choice
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
	v.noteIs(env.sink, t)
	return t
}

// checkRecursion looks at every call for a way back to the function under
// verification; see callgraph.go. A cycle that goes only through calls that
// name their callee needs a Variant on each function of it, decreasing at
// the call; one that goes through a call with no static callee, of an
// interface method or a function value, or through code of another
// package, is reported: no Variant can be checked across such a call.
// Calls that a function used as a value makes are not recursion of the
// function around it, and stratification bounds them.
func (v *fnVerifier) checkRecursion(callee *funcInfo, pre *specEnv, st *state, guard []*logic.Term, call *ast.CallExpr) {
	self := v.callGraph().byObj[v.fn.obj]
	if self == nil || v.fn.decl == nil || v.fn.spelled != nil {
		return
	}
	first := v.callEdges(call, callee)
	through, direct := v.cycleThrough(self, first, false), v.cycleThrough(self, first, true)
	// A trusted function of this package has a body to verify instead.
	if callee.trust != nil && byFunc(v.callGraph().byObj, v.pkgVerifier.originOf(callee.obj)) != nil && (through != nil || direct != nil) {
		shown := direct
		if shown == nil {
			shown = through
		}
		remedy := fmt.Sprintf("verify %s instead of trusting it", callee.obj.Name())
		if v.pkgVerifier.instanceOf[callee.obj] != nil {
			remedy = fmt.Sprintf("%s is generic and cannot be verified yet, so break the cycle", callee.obj.Name())
		}
		v.report(call.Pos(), "%s is trusted and calls back into %s, so that this call ends cannot be proved; %s; the cycle: %s",
			callee.obj.Name(), v.fn.obj.Name(), remedy, v.describeCycle(shown))
		return
	}
	if through != nil {
		// An edge into code of another package that only the types allow
		// is one the user cannot see; the message says what makes it.
		for _, step := range through.steps {
			if step.why != "" {
				why, advice, ok := strings.Cut(step.why, "\n")
				if !ok {
					advice = "Hand that code a value whose type holds no interface value and no function value, or keep what it may reach from calling back"
				}
				v.report(call.Pos(), "this call may not end: %s; %s, so a cycle goes through code of another package, and no Variant can be checked across it; %s",
					v.describeCycle(through), why, advice)
				return
			}
		}
		v.report(call.Pos(), "this call may not end: %s; a cycle that goes through a call with no static callee, of an interface method or "+
			"a function value, or through code of another package, cannot be shown to end, since no Variant can be checked across such a call. "+
			"Break the cycle", v.describeCycle(through))
	}
	if direct == nil {
		return
	}
	shown := "; the cycle: " + v.describeCycle(direct)
	for _, fn := range []*funcInfo{v.fn, callee} {
		if fn.measure == nil {
			v.report(call.Pos(), "recursive call needs a // @Variant annotation in the doc comment of %s to prove termination%s", fn.obj.Name(), shown)
			return
		}
	}
	measure := v.intTerm(callee.measure, pre)
	v.check(st, guard, logic.Lt(measure, v.measure), call.Pos(),
		"variant may not decrease in recursive call: %s", callee.measure.text)
}
