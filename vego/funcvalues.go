package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/types/typeutil"
)

// A function value has the contract of its type. A named function type
// declares one in its doc comment, with the Requires, Ensures, and Modifies
// annotations a function has, over the parameters and results its signature
// names:
//
//	// @Requires c != nil
//	// @Modifies c
//	type Option func(c *Config)
//
// A call through a value of such a type is checked like a call of a
// function with that contract. A value of a function type without a
// contract can be held and passed on, but not called. Nothing else is known
// of a value than whether it is nil.
//
// Such a contract is not verified: it describes every value of the type,
// and each value is checked against it where verified code makes it. A
// value that arrives from code that is not verified is taken to meet it.
// So a call through a value is treated, where the two differ, like a call
// of a trusted function: what it promises is checked against what is known
// at the call, nothing is assumed of the invariants of what it hands back,
// and a contract that leaves failure open makes the call a source of
// unpredictable failure.

// addTypeContract records an annotation written in the doc comment of a
// named function type.
func (pv *pkgVerifier) addTypeContract(name *types.TypeName, c *clause) {
	named, isNamed := name.Type().(*types.Named)
	switch {
	case c.kind != "Requires" && c.kind != "Ensures" && c.kind != "Modifies":
		pv.unread = true
		pv.report(c.pos, "%s annotations do not belong on a function type; a function type can only have Requires, Ensures, and Modifies annotations", c.kind)
		return
	case !isNamed || name.IsAlias():
		pv.unread = true
		pv.report(c.pos, "a contract can only be declared on a defined function type, not on an alias")
		return
	case named.TypeParams() != nil:
		pv.unread = true
		pv.report(c.pos, "a contract on a function type with type parameters is not supported yet")
		return
	}
	fn := pv.funcTypes[name]
	if fn == nil {
		sig := name.Type().Underlying().(*types.Signature)
		fn = newFuncInfo(types.NewFunc(name.Pos(), pv.pass.Pkg, name.Name(), sig))
		fn.valueOf = name
		pv.funcTypes[name] = fn
	}
	if c.kind == "Modifies" {
		targets, err := logic.ParseTargets(c.text)
		if err != nil {
			pv.report(c.pos, "syntax error in Modifies annotation: %v", err)
			fn.broken = true
			return
		}
		fn.modifies = append(fn.modifies, newModTargets(targets, c)...)
		return
	}
	node, err := logic.ParseFormula(c.text)
	if err != nil {
		pv.report(c.pos, "syntax error in %s annotation: %v", c.kind, err)
		fn.broken = true
		return
	}
	c.node = node
	if c.kind == "Requires" {
		fn.requires = append(fn.requires, c)
	} else {
		fn.ensures = append(fn.ensures, c)
	}
}

// checkTypeContracts checks the contract of every named function type of
// the package once, whether or not anything uses the type: its results have
// names, its parameters and results have types vego models, every name it
// uses means something, its Requires clauses can be met, and what it
// promises does not contradict itself.
func (pv *pkgVerifier) checkTypeContracts() {
	names := make([]*types.TypeName, 0, len(pv.funcTypes))
	for name := range pv.funcTypes {
		names = append(names, name)
	}
	slices.SortFunc(names, func(a, b *types.TypeName) int { return int(a.Pos() - b.Pos()) })
	for _, name := range names {
		fn := pv.funcTypes[name]
		sig := fn.obj.Type().(*types.Signature)
		if sig.Variadic() {
			pv.report(name.Pos(), "a contract on a variadic function type is not supported yet")
			fn.broken = true
		}
		for _, result := range fn.results {
			if result.Name() == "" || result.Name() == "_" {
				pv.report(name.Pos(), "%s has a contract, so each of its results needs a name, as in type %s func(...) (n int)", name.Name(), name.Name())
				fn.broken = true
				break
			}
		}
		for _, variable := range slices.Concat(fn.params, fn.results) {
			if _, ok := layoutOf(variable.Type()); !ok {
				pv.report(name.Pos(), "%s has a contract, and its %s has type %s, which is not supported", name.Name(), describe(variable), variable.Type())
				fn.broken = true
			}
			if variable.Name() != "" && fn.ambiguous(variable.Name(), false) {
				pv.report(name.Pos(), "%s names %s, which means something else in annotations; rename it", name.Name(), variable.Name())
				fn.broken = true
			}
		}
		if fn.broken {
			continue
		}
		pv.run(fn, func(v *fnVerifier) {
			v.misreadAs = func(c *clause, err error) {
				fn.broken = true
				pv.report(c.pos, "in %s annotation: %v", c.kind, err)
			}
			entry := v.enter()
			if v.quickly(entry, nil, logic.False()) {
				fn.broken = true
				pv.report(name.Pos(), "nothing can satisfy the Requires clauses of %s together with what the types of its parameters guarantee, "+
					"so no value of the type could be called", name.Name())
				return
			}
			v.primedPaths(fn)
			for _, defect := range fn.defects {
				pv.report(name.Pos(), "the contract of %s cannot be used: %s", name.Name(), defect)
			}
			if _, post, _ := v.contractInstance(entry); pv.contradictory(post) {
				fn.broken = true
				pv.report(name.Pos(), "the contract of %s contradicts itself, so a call of a value of the type would prove anything", name.Name())
				return
			}
			if !v.canBeMet(entry) {
				fn.broken = true
				pv.report(name.Pos(), "the Ensures clauses of %s are not proved to be satisfiable for every call that its Requires allow, "+
					"by results and a change of what Modifies lists; a value of the type is taken to meet them, so a call of one could prove something false", name.Name())
			}
		})
	}
}

// canBeMet reports whether, in every state its Requires allow, some outcome
// of a call meets the contract of the function type being checked. A value
// that comes from code that is not verified is taken to meet the contract.
// A contract that cannot be met for some call would make what it promises
// there a fact about the arguments, as 2 * y = x would make x even.
//
// The outcome is built so that Z3 only has to choose numbers: the results,
// the bound of what exists afterwards, and, for each struct or field that
// Modifies lists, a value written there. Slices and maps that Modifies
// lists keep their contents. A contract that can only be met by changing
// those, or by memory the call creates, is reported, which errs towards
// refusing.
func (v *fnVerifier) canBeMet(entry *state) bool {
	fn := v.fn
	st := entry.clone()
	mark, known := len(v.made), len(st.hyps)
	st.brk = v.fresh("brk", logic.Ref)
	st.assume(logic.Le(entry.brk, st.brk))
	for _, m := range fn.modifies {
		_, t, err := v.locateTarget(fn, m, v.entry, st, memory{})
		covered := coveredType(fn, m)
		if err != nil || !t.single || covered == nil {
			continue
		}
		if object, isPointer := pointee(covered); isPointer {
			covered = object
		}
		v.put(st, t.cells, t.ref, t.lo, v.unknown("out", covered, st))
	}
	results := make([]value, len(fn.results))
	for i, result := range fn.results {
		results[i] = v.unknown("out", result.Type(), st)
	}
	env := &specEnv{v: v, sink: st, fn: fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: entry.brk}
	var promised []*logic.Term
	for _, c := range fn.ensures {
		promised = append(promised, v.calleeFormula(c, env))
	}
	facts := append(slices.Clip(st.hyps[known:]), promised...)
	return v.proves(entry.hyps, v.someOutcome(facts, v.made[mark:]), 0)
}

// someOutcome states that some outcome of a call has the facts given: the
// constants that stand for what the call produced, among made, are bound
// by an existential quantifier.
func (v *fnVerifier) someOutcome(facts []*logic.Term, made []string) *logic.Term {
	produced := map[string]bool{}
	for _, name := range made {
		produced[name] = true
	}
	sorts := map[string]logic.Sort{}
	var order []string
	var collect func(t *logic.Term)
	seen := map[*logic.Term]bool{}
	collect = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		if t.Op == logic.OpConst && produced[t.Name] {
			if _, known := sorts[t.Name]; !known {
				order = append(order, t.Name)
			}
			sorts[t.Name] = t.Sort
		}
		for _, arg := range t.Args {
			collect(arg)
		}
	}
	body := logic.And(facts...)
	collect(body)
	bound := map[string]*logic.Term{}
	for _, name := range order {
		bound[name] = v.bound("out")
		bound[name] = logic.Bound(bound[name].Name, sorts[name])
	}
	body = substituteConsts(body, bound, map[*logic.Term]*logic.Term{})
	for _, name := range slices.Backward(order) {
		body = logic.Exists(bound[name], body)
	}
	return body
}

// substituteConsts replaces constants by the terms given for their names.
func substituteConsts(t *logic.Term, by map[string]*logic.Term, memo map[*logic.Term]*logic.Term) *logic.Term {
	if done, ok := memo[t]; ok {
		return done
	}
	result := t
	switch {
	case t.Op == logic.OpConst && by[t.Name] != nil:
		result = by[t.Name]
	case len(t.Args) > 0:
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = substituteConsts(arg, by, memo)
			changed = changed || args[i] != arg
		}
		if changed {
			result = logic.WithArgs(t, args)
		}
	}
	memo[t] = result
	return result
}

// exportTypeContracts publishes the contracts of the function types of the
// package. A value of an unexported type can reach another package too.
func (pv *pkgVerifier) exportTypeContracts() {
	for name, fn := range pv.funcTypes {
		if name.Parent() != pv.pass.Pkg.Scope() {
			continue
		}
		fact := pv.contractFactOf(fn, name.Pos())
		fact.Verified = !fn.broken && !pv.unread && !pv.predicatesBroken
		pv.pass.ExportObjectFact(name, fact)
	}
}

// valueContract returns the contract that a call through a value of a type
// is checked against, or nil if the type has none.
func (pv *pkgVerifier) valueContract(t types.Type) *funcInfo {
	named, ok := types.Unalias(t).(*types.Named)
	if !ok || !isFunc(t) {
		return nil
	}
	name := named.Origin().Obj()
	if name.Pkg() == pv.pass.Pkg {
		return pv.funcTypes[name]
	}
	if fn, done := pv.importedTypes[name]; done {
		return fn
	}
	pv.importedTypes[name] = nil
	fact := &contractFact{}
	if name.Pkg() == nil || !pv.pass.ImportObjectFact(name, fact) {
		return nil
	}
	sig := name.Type().Underlying().(*types.Signature)
	fn := pv.contractFromFact(types.NewFunc(name.Pos(), name.Pkg(), name.Name(), sig), name.Pkg(), fact)
	if !fact.Verified {
		fn.defects = []string{fmt.Sprintf("the annotations of package %s were not all read", name.Pkg().Path())}
	}
	fn.valueOf = name
	pv.importedTypes[name] = fn
	return fn
}

// usableValueContract returns the contract of the type of a function value
// that is called, or stops the verification when there is none or it cannot
// be used.
func (v *fnVerifier) usableValueContract(fun ast.Expr) *funcInfo {
	t := v.info.TypeOf(fun)
	fn := v.valueContract(t)
	if fn == nil {
		v.unsupported(fun.Pos(), fmt.Sprintf("%s has type %s, which has no contract; "+
			"declare a named function type with a contract and use it here", types.ExprString(fun), t))
	}
	for _, defect := range fn.defects {
		v.report(fun.Pos(), "the contract of %s cannot be used: %s", fn.obj.Name(), defect)
	}
	if fn.broken {
		v.unsupported(fun.Pos(), fmt.Sprintf("the contract of %s could not be understood", fn.obj.Name()))
	}
	sig := fn.obj.Type().(*types.Signature)
	if sig.Variadic() {
		v.unsupported(fun.Pos(), "calls of variadic function values are not supported yet")
	}
	return fn
}

// callValue verifies a call through a function value. The value and the
// arguments are evaluated before the call, which is an event of the unit
// like any call; then the value must not be nil, and the contract of its
// type applies.
func (v *fnVerifier) callValue(call *ast.CallExpr, st *state, guard []*logic.Term) []value {
	fn := v.usableValueContract(call.Fun)
	u := v.unit
	operands := u.pushCeiling()
	fun, args := v.valueOperands(call, fn, st, guard)
	u.reach(operands)
	name := types.ExprString(call.Fun)
	v.check(st, guard, logic.Ne(fun[0], logic.RefLit(0)), call.Pos(), "the function value %s may be nil", name)
	results := v.invoke(call, fn, args, st, guard)
	u.calls = append(u.calls, unitCall{name: name, pos: call.Pos(), pure: len(fn.modifies) == 0 && signatureMemoryFree(fn.obj.Type().(*types.Signature))})
	u.event()
	return results
}

// valueOperands evaluates the function value of a call and its arguments,
// and refuses an argument that carries code nobody has seen.
func (v *fnVerifier) valueOperands(call *ast.CallExpr, fn *funcInfo, st *state, guard []*logic.Term) (value, map[*types.Var]value) {
	if len(call.Args) != len(fn.params) {
		v.unsupported(call.Pos(), "a call with several results as the arguments of another call is not supported yet")
	}
	fun := v.eval(call.Fun, st, guard)
	args := map[*types.Var]value{}
	for i, arg := range call.Args {
		args[fn.params[i]] = v.evalAs(arg, fn.params[i].Type(), st, guard)
	}
	v.checkHandedToValue(call, fn)
	return fun, args
}

// deferValue executes the defer of a call through a function value: the
// value and the arguments are settled now, and the call runs when the frame
// returns. A nil value would panic then; it is reported here, where the
// value is fixed.
func (v *fnVerifier) deferValue(s *ast.DeferStmt, st *state) {
	fn := v.usableValueContract(s.Call.Fun)
	var fun value
	var args map[*types.Var]value
	v.evaluate(st, func() {
		defer v.begin()()
		fun, args = v.valueOperands(s.Call, fn, st, nil)
	})
	v.check(st, nil, logic.Ne(fun[0], logic.RefLit(0)), s.Call.Pos(), "the function value %s may be nil", types.ExprString(s.Call.Fun))
	st.deferred = append(slices.Clip(st.deferred), deferredCall{call: s.Call, fn: fn, args: args})
}

// checkHandedToValue refuses an argument of a call through a function value
// that carries code nobody has seen. The value may come from code that is
// not verified, which could run that code, and its contract would then not
// say what the call does: an error of unknown origin, whose methods could
// write memory, a function value whose type has no contract, or anything
// else that can hold an interface. A function value of a type with a
// contract and an error of known origin carry no such code.
func (v *fnVerifier) checkHandedToValue(call *ast.CallExpr, fn *funcInfo) {
	for i, arg := range call.Args {
		t := fn.params[i].Type()
		if isError(t) {
			if v.knownError(v.bodyOrigins(), arg, -1, map[*types.Var]bool{}) {
				continue
			}
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to the function value %s and is an error whose origin is not known%s; "+
				"the value may come from code that is not verified, which could run code through it that nobody has seen",
				types.ExprString(arg), types.ExprString(call.Fun), v.originWhy(arg)))
		}
		if what := v.foreignCode(t, map[types.Type]bool{}); what != "" {
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to the function value %s and is a value of type %s, which can hold %s; "+
				"the value may come from code that is not verified, which could run code through it that nobody has seen",
				types.ExprString(arg), types.ExprString(call.Fun), t, what))
		}
	}
}

// foreignCode says what code a value of a type can hold, however deep, that
// nothing describes: an interface, a function value whose type has no
// contract, or a channel through which either may arrive. It returns ""
// when there is none.
func (pv *pkgVerifier) foreignCode(t types.Type, seen map[types.Type]bool) string {
	if t == nil || seen[t] {
		return ""
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Interface:
		return "an error, or another interface"
	case *types.Chan:
		return "a channel"
	case *types.Signature:
		if pv.valueContract(t) == nil {
			return "a function value whose type has no contract"
		}
	case *types.Pointer:
		return pv.foreignCode(u.Elem(), seen)
	case *types.Slice:
		return pv.foreignCode(u.Elem(), seen)
	case *types.Array:
		return pv.foreignCode(u.Elem(), seen)
	case *types.Map:
		if what := pv.foreignCode(u.Key(), seen); what != "" {
			return what
		}
		return pv.foreignCode(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if what := pv.foreignCode(field.Type(), seen); what != "" {
				return what
			}
		}
	}
	return ""
}

// holdsContractedValue reports whether a value of a type can hold, however
// deep, through pointers, slices, and maps, a function value of a type with
// a contract.
func (pv *pkgVerifier) holdsContractedValue(t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return pv.valueContract(t) != nil
	case *types.Pointer:
		return pv.holdsContractedValue(u.Elem(), seen)
	case *types.Slice:
		return pv.holdsContractedValue(u.Elem(), seen)
	case *types.Array:
		return pv.holdsContractedValue(u.Elem(), seen)
	case *types.Map:
		return pv.holdsContractedValue(u.Key(), seen) || pv.holdsContractedValue(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if pv.holdsContractedValue(field.Type(), seen) {
				return true
			}
		}
	}
	return false
}

// holdsFunc reports whether a value of a type can hold, however deep, a
// function value of any type.
func holdsFunc(t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return true
	case *types.Pointer:
		return holdsFunc(u.Elem(), seen)
	case *types.Slice:
		return holdsFunc(u.Elem(), seen)
	case *types.Array:
		return holdsFunc(u.Elem(), seen)
	case *types.Map:
		return holdsFunc(u.Key(), seen) || holdsFunc(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if holdsFunc(field.Type(), seen) {
				return true
			}
		}
	}
	return false
}

// mayCallValues reports whether running a function may make a call through
// a function value, in its own body or in what it calls. A function whose
// body is in this package is judged by its body: a call that has no static
// callee, a range over a function, and a call of a function that may. One
// verified in another package says so in its contract. A trusted function
// may when its contract lists, under runs, a parameter that can hold a
// function value. A function without a contract or a body may.
func (pv *pkgVerifier) mayCallValues(obj *types.Func) bool {
	if pv.mayCall == nil {
		pv.mayCall = map[*types.Func]bool{}
		pv.findValueCallers()
	}
	if may, known := pv.mayCall[obj.Origin()]; known {
		return may
	}
	may := true
	switch fn := pv.contractOf(obj.Origin()); {
	case fn == nil:
	case fn.imported != nil:
		may = fn.imported.CallsValues
	case fn.trust != nil:
		may = false
		for param := range fn.runs {
			may = may || holdsFunc(param.Type(), map[types.Type]bool{})
		}
	}
	pv.mayCall[obj.Origin()] = may
	return may
}

// findValueCallers decides mayCallValues for every function of the package
// that has a body, as the least set closed under calls: a function is in it
// when its body makes a call through a function value, or calls a function
// that is in it. A trusted function of the package is judged by its body
// too, which is there to read, as well as by its contract: one whose body
// calls a function value kept in a variable makes such a call whatever its
// runs says.
func (pv *pkgVerifier) findValueCallers() {
	calls := map[*types.Func][]*types.Func{}
	var pending []*types.Func
	for _, fn := range pv.order {
		if fn.decl.Body == nil {
			continue
		}
		direct := false
		if trusted := pv.trustedContract(fn.obj); trusted != nil {
			for param := range trusted.runs {
				direct = direct || holdsFunc(param.Type(), map[types.Type]bool{})
			}
		}
		bound, _ := literalUses(pv.info, fn.decl.Body)
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.RangeStmt:
				direct = direct || rangesByCalling(pv.info.TypeOf(n.X))
			case *ast.CallExpr:
				tv := pv.info.Types[n.Fun]
				if tv.IsType() || tv.IsBuiltin() {
					break
				}
				if callee := typeutil.StaticCallee(pv.info, n); callee != nil {
					calls[fn.obj] = append(calls[fn.obj], callee.Origin())
					break
				}
				switch fun := ast.Unparen(n.Fun).(type) {
				case *ast.FuncLit:
					return true
				case *ast.Ident:
					if variable, ok := pv.info.Uses[fun].(*types.Var); ok && bound[variable] != nil {
						return true
					}
				}
				direct = true
			}
			return true
		})
		pv.mayCall[fn.obj] = direct
		if direct {
			pending = append(pending, fn.obj)
		}
	}
	// What calls a function that may make such a call may make one too.
	callers := map[*types.Func][]*types.Func{}
	for caller, callees := range calls {
		for _, callee := range callees {
			if _, local := pv.mayCall[callee]; !local && pv.mayCallValues(callee) {
				if !pv.mayCall[caller] {
					pv.mayCall[caller] = true
					pending = append(pending, caller)
				}
			}
			callers[callee] = append(callers[callee], caller)
		}
	}
	for len(pending) > 0 {
		callee := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		for _, caller := range callers[callee] {
			if !pv.mayCall[caller] {
				pv.mayCall[caller] = true
				pending = append(pending, caller)
			}
		}
	}
}

// coveredType returns the type a Modifies entry ends in: the pointer, slice,
// or map whose memory it covers, or the field it names. It returns nil for
// an entry that does not follow the types, which is reported elsewhere.
func coveredType(fn *funcInfo, m *modTarget) types.Type {
	param, ok := fn.paramNames[m.name]
	if !ok {
		return nil
	}
	steps := make([]logic.Step, len(m.steps))
	for i, step := range m.steps {
		steps[i] = logic.Step{Field: step.field}
		if step.index == nil {
			continue
		}
		_, indexed, err := plan(param.Type(), steps[:i])
		if err != nil {
			return nil
		}
		steps[i].Index = logic.IntLit(0)
		if isMap(indexed) && isString(indexed.Underlying().(*types.Map).Key()) {
			steps[i].Index = logic.Fill(logic.IntLit(0), logic.IntLit(0))
		}
	}
	_, final, err := plan(param.Type(), steps)
	if err != nil {
		return nil
	}
	return final
}

// A value of a function type with a contract is made in one of these ways,
// where Go converts it to the type: from a function literal, a function, or
// a method value written there; from nil; or from a value of the same type.
// The first three are checked against the contract of the type there, as a
// function of their own: in a state with memory of its own, knowing of
// what they capture only its value where the value is made. Every other way
// is refused, since nothing would show that the value meets the contract.
// So is making a value of a function type that has no contract.

// functionValue evaluates an expression that is assigned to something of a
// function type.
func (v *fnVerifier) functionValue(e ast.Expr, want types.Type, st *state, guard []*logic.Term) value {
	inner := ast.Unparen(e)
	named, method := v.valueForm(inner)
	_, isLiteral := inner.(*ast.FuncLit)
	if named == nil && method == nil && !isLiteral {
		if !types.Identical(v.info.TypeOf(e), want) {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s to %s is not supported: a value of a function type is made only from "+
				"a function literal, a function, or a method value written there, from nil, or from a value of the same type",
				types.ExprString(e), want))
		}
		return v.eval(e, st, guard)
	}
	T := v.valueContract(want)
	if T == nil {
		v.unsupported(e.Pos(), fmt.Sprintf("%s is used as a value of type %s, which has no contract; "+
			"declare a named function type with a contract and use it here", types.ExprString(e), want))
	}
	for _, defect := range T.defects {
		v.report(e.Pos(), "the contract of %s cannot be used: %s", T.obj.Name(), defect)
	}
	if T.broken {
		v.unsupported(e.Pos(), fmt.Sprintf("the contract of %s could not be understood", T.obj.Name()))
	}
	switch {
	case isLiteral:
		v.unsupported(e.Pos(), "a function literal is supported only where it is called or deferred, or as the value "+
			"that declares a new variable which is only ever called; this one is used as a value")
	case named != nil:
		v.madeFrom(e, T, named, nil, st, guard)
	default:
		sel := inner.(*ast.SelectorExpr)
		recv := method.Type().(*types.Signature).Recv()
		// The receiver is evaluated where the method value is made, as for
		// a call: a pointer receiver takes the address of a variable, and a
		// value receiver copies the struct, which a nil pointer cannot.
		var receiver value
		func() {
			defer v.begin()()
			receiver = v.receiver(&ast.CallExpr{Fun: sel, Lparen: sel.End(), Rparen: sel.End()}, recv, st, guard)
		}()
		v.madeFrom(e, T, method, receiver, st, guard)
	}
	return value{logic.RefLit(1)}
}

// valueForm returns the function, or the method of a method value, that an
// expression names, if it is one of those. A method expression, T.M, is
// neither and is refused.
func (v *fnVerifier) valueForm(e ast.Expr) (named, method *types.Func) {
	switch e := e.(type) {
	case *ast.Ident:
		named, _ = v.info.Uses[e].(*types.Func)
	case *ast.SelectorExpr:
		if selection := v.info.Selections[e]; selection != nil {
			switch selection.Kind() {
			case types.MethodVal:
				method, _ = selection.Obj().(*types.Func)
			case types.MethodExpr:
				v.unsupported(e.Pos(), "a method expression, as in T.M, cannot be used as a value yet; use a method value, as in x.M, or a function literal")
			}
			break
		}
		named, _ = v.info.Uses[e.Sel].(*types.Func)
	}
	return named, method
}

// madeFrom checks that a function, or a method on a receiver, meets the
// contract of the function type it is used as. It is checked as a
// function of its own that calls it: called in a state where the Requires
// of the type hold, with memory of its own, it must meet the Requires of
// the function, write nothing the type does not list, and leave the Ensures
// of the type true. What it runs must make no call through a function
// value.
func (v *fnVerifier) madeFrom(e ast.Expr, T *funcInfo, callee *types.Func, receiver value, st *state, guard []*logic.Term) {
	sig := callee.Type().(*types.Signature)
	if sig.Variadic() || sig.TypeParams() != nil || sig.RecvTypeParams() != nil {
		v.unsupported(e.Pos(), "variadic and generic functions cannot be used as values yet")
	}
	fn := v.contractOf(callee)
	if fn == nil {
		v.unsupported(e.Pos(), fmt.Sprintf("it uses %s as a value, and %s has no contract; annotate %s with // @ annotations so that it is verified, "+
			"or add a trusted contract for %s to %s", callee.Name(), callee.Name(), callee.Name(), callee.FullName(), TrustFileName))
	}
	for _, defect := range fn.defects {
		v.report(e.Pos(), "the contract of %s cannot be used: %s", callee.FullName(), defect)
	}
	if fn.broken {
		v.unsupported(e.Pos(), callee.Name()+" has a contract that could not be understood")
	}
	// What a value made by verified code runs may make no call through a
	// function value. No contract of a function type has a variant, so
	// nothing would then prove that a chain of such calls ends: a value
	// could be handed back to code that calls it again. With this rule a
	// call through a value made by verified code runs code that makes no
	// such call.
	if v.pkgVerifier.mayCallValues(callee) {
		v.unsupported(e.Pos(), fmt.Sprintf("%s may call through a function value, and code that a function value runs cannot do that yet: "+
			"no contract of a function type has a variant, so nothing would prove that such calls end", callee.Name()))
	}
	site := v.site(e.Pos(), "in %s used as a %s at %s", types.ExprString(e), T.obj.Name(), v.placeOf(e.Pos()))
	sv, entry, carry := v.subVerifier(T, st, guard, site)
	// The arguments of the call: the receiver as it was where the value
	// was made, and the parameters of the type in order.
	args := map[*types.Var]value{}
	var inputs []*types.Var
	if sig.Recv() != nil {
		args[fn.params[0]] = carry.value(receiver)
		inputs = fn.params[1:]
	} else {
		inputs = fn.params
	}
	call := &ast.CallExpr{Fun: e, Lparen: e.End(), Rparen: e.End()}
	for i, param := range inputs {
		args[param] = sv.entry[T.params[i]]
		call.Args = append(call.Args, &ast.Ident{NamePos: e.Pos(), Name: T.params[i].Name()})
	}
	if fn.trust != nil {
		v.noteUse(fn, e.Pos())
		// The parameters of the value come from whoever calls it, so what
		// can carry code is handed on to the trusted function unseen.
		for _, param := range inputs {
			if fn.runs[param] || !holdsCode(param.Type(), map[types.Type]bool{}) {
				continue
			}
			v.unsupported(e.Pos(), fmt.Sprintf("%s is used as a value, which passes what it is called with to %s as %s; "+
				"%s is trusted, and that can hold code nobody has seen. If its contract holds whatever that code does, "+
				"list %s under runs in the contract", types.ExprString(e), fn.obj.Name(), param.Name(), fn.obj.Name(), param.Name()))
		}
	}
	results := sv.invoke(call, fn, args, entry, nil)
	sv.atReturn(entry, results, e.Pos())
}

// subVerifier returns a verifier for a function value that is made in a
// state: a function of its own with the contract of its type, whose entry
// state holds its parameters as the contract describes them, memory of its
// own, and a copy of the state where the value is made, in which every
// constant is renamed. The copy tells what is known of the values the
// function value keeps, and nothing of the memory it sees when it runs.
// carry renames values of the state where the value is made into the copy.
func (v *fnVerifier) subVerifier(fn *funcInfo, st *state, guard []*logic.Term, site inlineSite) (sv *fnVerifier, entry *state, carry *transport) {
	sv = v.newVerifier(fn)
	sv.originBody = v.bodyOrigin()
	sv.boxed = v.boxed
	sv.sites = append(slices.Clip(v.sites), site)
	// The names of the copy cannot be those of the verifier that reads it.
	// A copy made inside a copy renames the names of the outer copy again,
	// so they stay apart from both.
	carry = &transport{prefix: transportMark + " ", memo: map[*logic.Term]*logic.Term{}}
	entry = sv.enter()
	for _, fact := range st.hyps {
		entry.assume(carry.term(fact))
	}
	for _, cond := range guard {
		entry.assume(carry.term(cond))
	}
	// Everything that existed where the value was made exists when it runs.
	entry.assume(logic.Le(carry.term(st.brk), entry.brk))
	return sv, entry, carry
}

// bodyOrigin returns the body bodyOrigins reads.
func (v *fnVerifier) bodyOrigin() *ast.BlockStmt {
	if v.originBody != nil {
		return v.originBody
	}
	if v.fn.decl != nil {
		return v.fn.decl.Body
	}
	return nil
}

// transportMark begins every name in a renamed copy of a state. No name the
// verifier makes begins with it; see fresh.
const transportMark = "^"

// transport renames the constants of terms into a namespace of its own,
// apart from the names of the verifier that reads them. The constants of
// error variables and nil are kept, since they mean the same everywhere.
type transport struct {
	prefix string
	memo   map[*logic.Term]*logic.Term
}

// term returns a term with its constants renamed.
func (tr *transport) term(t *logic.Term) *logic.Term {
	if renamed, done := tr.memo[t]; done {
		return renamed
	}
	var renamed *logic.Term
	switch {
	case t == logic.NilErr() || isSentinelTerm(t):
		renamed = t
	case t.Op == logic.OpConst:
		renamed = logic.Const(tr.prefix+t.Name, t.Sort)
	case t.Op == logic.OpBound:
		renamed = logic.Bound(tr.prefix+t.Name, t.Sort)
	case len(t.Args) == 0:
		renamed = t
	default:
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = tr.term(arg)
			changed = changed || args[i] != arg
		}
		renamed = t
		if changed {
			renamed = logic.WithArgs(t, args)
		}
	}
	tr.memo[t] = renamed
	return renamed
}

// value renames the leaves of a value.
func (tr *transport) value(val value) value {
	if val == nil {
		return nil
	}
	renamed := make(value, len(val))
	for i, leaf := range val {
		renamed[i] = tr.term(leaf)
	}
	return renamed
}
