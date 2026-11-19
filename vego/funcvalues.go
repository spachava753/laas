package vego

import (
	"fmt"
	"go/ast"
	"go/token"
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
	pv.addValueClause(fn, c)
}

// addValueClause records a Requires, Ensures, or Modifies annotation of the
// contract of a function type or of a method of an interface type.
func (pv *pkgVerifier) addValueClause(fn *funcInfo, c *clause) {
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
	var contracts []*funcInfo
	for _, fn := range pv.funcTypes {
		contracts = append(contracts, fn)
	}
	for _, fn := range pv.ifaceMethods {
		contracts = append(contracts, fn)
	}
	slices.SortFunc(contracts, func(a, b *funcInfo) int { return int(a.obj.Pos() - b.obj.Pos()) })
	for _, fn := range contracts {
		pv.checkValueContract(fn)
	}
	pv.checkDroppedContracts()
}

// checkValueContract checks the contract of a function type or of a method
// of an interface type where it is declared.
func (pv *pkgVerifier) checkValueContract(fn *funcInfo) {
	// The contract is named as the type, or as the interface and the
	// method.
	at, title := fn.obj.Pos(), fn.obj.Name()
	example := fmt.Sprintf("type %s func(...) (n int)", title)
	if fn.methodOf != nil {
		title = methodTitle(fn.methodOf)
		example = fmt.Sprintf("%s(...) (n int)", fn.methodOf.Name())
	}
	sig := fn.obj.Type().(*types.Signature)
	if sig.Variadic() {
		what := "function type"
		if fn.methodOf != nil {
			what = "method of an interface"
		}
		pv.report(at, "a contract on a variadic %s is not supported yet", what)
		fn.broken = true
	}
	for _, result := range fn.results {
		if result.Name() == "" || result.Name() == "_" {
			pv.report(at, "%s has a contract, so each of its results needs a name, as in %s", title, example)
			fn.broken = true
			break
		}
	}
	for _, variable := range slices.Concat(fn.params, fn.results) {
		if _, ok := layoutOf(variable.Type()); !ok {
			pv.report(at, "%s has a contract, and its %s has type %s, which is not supported", title, describe(variable), variable.Type())
			fn.broken = true
		}
		if variable.Name() != "" && fn.ambiguous(variable.Name(), false) {
			pv.report(at, "%s names %s, which means something else in annotations; rename it", title, variable.Name())
			fn.broken = true
		}
	}
	if fn.broken {
		return
	}
	pv.run(fn, func(v *fnVerifier) {
		v.misreadAs = func(c *clause, err error) {
			fn.broken = true
			pv.report(c.pos, "in %s annotation: %v", c.kind, err)
		}
		entry := v.enter()
		if v.quickly(entry, nil, logic.False()) {
			fn.broken = true
			pv.report(at, "nothing can satisfy the Requires clauses of %s together with what the types of its parameters guarantee, "+
				"so no value of the type could be called", title)
			return
		}
		v.primedPaths(fn)
		for _, defect := range fn.defects {
			pv.report(at, "the contract of %s cannot be used: %s", title, defect)
		}
		if _, post, _ := v.contractInstance(entry); pv.contradictory(post) {
			fn.broken = true
			pv.report(at, "the contract of %s contradicts itself, so a call of a value of the type would prove anything", title)
			return
		}
		if !v.canBeMet(entry) {
			fn.broken = true
			pv.report(at, "the Ensures clauses of %s are not proved to be satisfiable for every call that its Requires allow, "+
				"by results and a change of what Modifies lists; a value of the type is taken to meet them, so a call of one could prove something false. "+
				"State in the Requires when some result exists, or weaken the Ensures", title)
		}
	})
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
	// Reading the Ensures notes facts, such as the range of a number read
	// from memory on entry. One that mentions nothing the outcome produced
	// is a fact about the entry state, which holds wherever that memory is
	// read; the rest is what the outcome has to meet.
	given := slices.Clip(entry.hyps)
	facts := promised
	for _, fact := range st.hyps[known:] {
		if mentionsAny(fact, v.made[mark:]) {
			facts = append(facts, fact)
		} else {
			given = append(given, fact)
		}
	}
	return v.proves(given, v.someOutcome(facts, v.made[mark:]), 0)
}

// mentionsAny reports whether a term mentions a constant of the given names.
func mentionsAny(t *logic.Term, names []string) bool {
	set := map[string]bool{}
	for _, name := range names {
		set[name] = true
	}
	_, mentioned := estranged(t, set)
	return mentioned
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
// package and of the methods of its interface types. A value of an
// unexported type can reach another package too.
func (pv *pkgVerifier) exportTypeContracts() {
	for name, fn := range pv.funcTypes {
		if name.Parent() != pv.pass.Pkg.Scope() {
			continue
		}
		fact := pv.contractFactOf(fn, name.Pos())
		fact.Verified = !fn.broken && !pv.unread && !pv.predicatesBroken
		pv.pass.ExportObjectFact(name, fact)
	}
	// A method of an interface type has a contract only when the type is
	// declared at package level.
	for method, fn := range pv.ifaceMethods {
		fact := pv.contractFactOf(fn, method.Pos())
		fact.Verified = !fn.broken && !pv.unread && !pv.predicatesBroken
		pv.pass.ExportObjectFact(method, fact)
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
	v.checkHandedToValue(call, fn, "the function value "+types.ExprString(call.Fun))
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
func (v *fnVerifier) checkHandedToValue(call *ast.CallExpr, fn *funcInfo, callee string) {
	for i, arg := range call.Args {
		t := fn.params[i].Type()
		if isError(t) {
			if v.knownError(v.bodyOrigins(), arg, -1, map[*types.Var]bool{}) {
				continue
			}
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to %s and is an error whose origin is not known%s; "+
				"the value may come from code that is not verified, which could run code through it that nobody has seen",
				types.ExprString(arg), callee, v.originWhy(arg)))
		}
		if what := v.foreignCode(t, map[types.Type]bool{}); what != "" {
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to %s and is a value of type %s, which can hold %s; "+
				"the value may come from code that is not verified, which could run code through it that nobody has seen",
				types.ExprString(arg), callee, t, what))
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
		// Every method of an interface with a contract on each is code
		// that meets its contract.
		if pv.fullyContracted(t) {
			return ""
		}
		if isIface(t) && u.NumMethods() > 0 {
			for method := range u.Methods() {
				if fn := pv.methodContract(method); fn != nil && fn.broken {
					return "an interface value with a method whose contract cannot be used"
				}
			}
			return "an interface value with a method that has no contract"
		}
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
// a contract, or an interface value with a method that has one.
func (pv *pkgVerifier) holdsContractedValue(t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return pv.valueContract(t) != nil
	case *types.Interface:
		// Verified code can call a method that has a contract, and only
		// such a method. Until type assertions are built, nothing else
		// that an interface holds can reach it: an interface without
		// contracts, any, and errors are left out, and must be counted
		// once they are.
		if !isIface(t) {
			return false
		}
		for method := range u.Methods() {
			if pv.methodContract(method) != nil {
				return true
			}
		}
		return false
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

// holdsCallable reports whether a value of a type can hold, however deep, a
// function value of any type, or an interface value with a method that has
// a contract. For those, runs claims only that the contract holds for
// values that meet their contracts, which a cycle back through code that
// verified code made would make circular. For an interface without
// contracts, any, and an error, runs claims that the contract holds
// whatever code arrives, and a cycle would make that claim false, which is
// on the author of the entry. Until type assertions are built, verified
// code also makes no value that such an interface holds and that it could
// call; they must be counted once it does.
func holdsCallable(pv *pkgVerifier, t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return true
	case *types.Interface:
		return pv.holdsContractedValue(t, map[types.Type]bool{})
	case *types.Pointer:
		return holdsCallable(pv, u.Elem(), seen)
	case *types.Slice:
		return holdsCallable(pv, u.Elem(), seen)
	case *types.Array:
		return holdsCallable(pv, u.Elem(), seen)
	case *types.Map:
		return holdsCallable(pv, u.Key(), seen) || holdsCallable(pv, u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if holdsCallable(pv, field.Type(), seen) {
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
	// A method of an interface runs whatever the value holds.
	if isIfaceMethod(obj) {
		return true
	}
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
		may = pv.runsValues(fn)
	}
	pv.mayCall[obj.Origin()] = may
	return may
}

// runsValues reports whether a trusted function may call a function value,
// or a method of an interface value with a contract, that it is given: one
// held, at any depth, by a parameter listed under runs, other than a
// function parameter with a contract under calls. What is handed over
// there is judged where it is handed over. See holdsCallable.
func (pv *pkgVerifier) runsValues(fn *funcInfo) bool {
	for param := range fn.runs {
		if fn.calls[param] == nil && holdsCallable(pv, param.Type(), map[types.Type]bool{}) {
			return true
		}
	}
	return false
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
	// local holds the functions judged by their bodies here. It is kept
	// apart from mayCall, which also caches what other functions are
	// judged to do as they are asked about.
	local := map[*types.Func]bool{}
	var pending []*types.Func
	for _, fn := range pv.order {
		if fn.decl.Body == nil {
			continue
		}
		local[fn.obj] = true
		direct := false
		trusted := pv.trustedContract(fn.obj)
		if trusted != nil {
			direct = pv.runsValues(trusted)
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
					// What a trusted function is handed to call runs as part
					// of this call: a literal is walked as part of the body,
					// a function or method is called, and anything else is a
					// call through a function value.
					for _, arg := range pv.handedArgs(n) {
						switch handed, isLit := pv.handedFunc(arg); {
						case isLit:
						case handed != nil:
							calls[fn.obj] = append(calls[fn.obj], handed.Origin())
						default:
							direct = true
						}
					}
					break
				}
				switch fun := ast.Unparen(n.Fun).(type) {
				case *ast.FuncLit:
					return true
				case *ast.Ident:
					if variable, ok := pv.info.Uses[fun].(*types.Var); ok && bound[variable] != nil {
						return true
					}
					// A trusted function that calls what it is handed under
					// calls runs code its caller hands over, which is
					// judged where it is handed over.
					if variable, ok := pv.info.Uses[fun].(*types.Var); ok && trusted != nil && trusted.calls[variable] != nil {
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
			if !local[callee] && pv.mayCallValues(callee) {
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
		what := types.ExprString(e)
		if isLiteral {
			what = "the function literal"
		}
		v.unsupported(e.Pos(), fmt.Sprintf("%s is used as a value of type %s, which has no contract; "+
			"declare a named function type with a contract and use it here", what, want))
	}
	for _, defect := range T.defects {
		v.report(e.Pos(), "the contract of %s cannot be used: %s", T.obj.Name(), defect)
	}
	if T.broken {
		v.unsupported(e.Pos(), fmt.Sprintf("the contract of %s could not be understood", T.obj.Name()))
	}
	switch {
	case isLiteral:
		v.madeLiteral(inner.(*ast.FuncLit), T, st, guard)
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
	site := v.site(e.Pos(), "in %s used as a value of type %s at %s", types.ExprString(e), T.obj.Name(), v.placeOf(e.Pos()))
	v.madeAs(e, e, T, callee, "a value", "a function value", site, func(_ *fnVerifier, _ *state, carry *transport) value {
		return carry.value(receiver)
	}, st, guard)
}

// madeAs checks that a function or method meets the contract T of what it
// is made into where e is converted: a value of a function type, or a
// method of an interface value. It is checked as a function of its own that
// calls it, written fun: called in a state where the Requires of T hold,
// with memory of its own, it must meet the Requires of the function, write
// nothing T does not list, and leave the Ensures of T true. What it runs
// must make no call through a function value or an interface value. as
// says what it is used as, and holder what holds it, in messages; receive
// gives the receiver of a method in the state of the check.
func (v *fnVerifier) madeAs(e, fun ast.Expr, T *funcInfo, callee *types.Func, as, holder string, site inlineSite,
	receive func(sv *fnVerifier, entry *state, carry *transport) value, st *state, guard []*logic.Term) {
	sig := callee.Type().(*types.Signature)
	if sig.Variadic() || sig.TypeParams() != nil || sig.RecvTypeParams() != nil {
		v.unsupported(e.Pos(), fmt.Sprintf("variadic and generic functions cannot be used as %s yet", as))
	}
	fn := v.contractOf(callee)
	if fn == nil {
		v.unsupported(e.Pos(), fmt.Sprintf("it uses %s as %s, and %s has no contract; annotate %s with // @ annotations so that it is verified, "+
			"or add a trusted contract for %s to %s", callee.Name(), as, callee.Name(), callee.Name(), callee.FullName(), TrustFileName))
	}
	for _, defect := range fn.defects {
		v.report(e.Pos(), "the contract of %s cannot be used: %s", callee.FullName(), defect)
	}
	if fn.broken {
		v.unsupported(e.Pos(), callee.Name()+" has a contract that could not be understood")
	}
	// What a value made by verified code runs may make no call through a
	// function value or an interface value. No contract of a function type
	// or an interface method has a variant, so nothing would then prove
	// that a chain of such calls ends: a value could be handed back to code
	// that calls it again. With this rule a call through a value made by
	// verified code runs code that makes no such call.
	if v.pkgVerifier.mayCallValues(callee) {
		v.unsupported(e.Pos(), fmt.Sprintf("%s may call through a function value or an interface value, and code that %s runs cannot do that yet: "+
			"no contract of a function type or of a method of an interface has a variant, so nothing would prove that such calls end", callee.Name(), holder))
	}
	sv, entry, carry := v.subVerifier(T, st, guard, site)
	if sig.Recv() != nil {
		contract, made := T.obj.Name(), as
		if T.methodOf == nil {
			contract, made = "the contract of "+T.obj.Name(), "a value of type "+T.obj.Name()
		}
		sv.heldReceiver = fn.params[0]
		sv.heldRemedy = fmt.Sprintf("%s can list only what its parameters refer to, so a method that writes what its receiver refers to "+
			"cannot be used as %s yet", contract, made)
	}
	// The arguments of the call: the receiver, and the parameters of T in
	// order.
	args := map[*types.Var]value{}
	var inputs []*types.Var
	if sig.Recv() != nil {
		args[fn.params[0]] = receive(sv, entry, carry)
		inputs = fn.params[1:]
	} else {
		inputs = fn.params
	}
	call := &ast.CallExpr{Fun: fun, Lparen: e.End(), Rparen: e.End()}
	for i, param := range inputs {
		args[param] = sv.entry[T.params[i]]
		call.Args = append(call.Args, &ast.Ident{NamePos: e.Pos(), Name: T.params[i].Name()})
	}
	if fn.trust != nil && len(fn.calls) > 0 {
		v.unsupported(e.Pos(), fmt.Sprintf("%s calls a function it is given, and cannot be used as %s: "+
			"what it would be given would come from code nobody has seen", callee.Name(), as))
	}
	if fn.trust != nil {
		v.noteUse(fn, e.Pos())
		// The receiver is handed to the trusted method at each call, as
		// at a call written out, where checkHandedOver looks at it. A
		// method whose entry lists it under runs may call through what it
		// holds, and is refused above.
		if recv := sig.Recv(); recv != nil && !fn.runs[fn.params[0]] && holdsCode(recv.Type(), map[types.Type]bool{}) {
			v.unsupported(e.Pos(), fmt.Sprintf("%s is used as %s, which hands its receiver to %s at each call; %s is trusted, and its receiver "+
				"is a value of type %s, which can hold an error, an interface, or a function, so %s could run code through it that nobody has seen. "+
				"If its contract holds whatever that code does, list %s under runs in the contract",
				types.ExprString(e), as, fn.obj.Name(), fn.obj.Name(), recv.Type(), fn.obj.Name(), fn.params[0].Name()))
		}
		// The parameters of the value come from whoever calls it, so what
		// can carry code is handed on to the trusted function unseen.
		for _, param := range inputs {
			if fn.runs[param] || !holdsCode(param.Type(), map[types.Type]bool{}) {
				continue
			}
			v.unsupported(e.Pos(), fmt.Sprintf("%s is used as %s, which passes what it is called with to %s as %s; "+
				"%s is trusted, and that can hold code nobody has seen. If its contract holds whatever that code does, "+
				"list %s under runs in the contract", types.ExprString(e), as, fn.obj.Name(), param.Name(), fn.obj.Name(), param.Name()))
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

// A function literal used as a value travels: it may run during the call it
// is handed to or long after, any number of times, while the function that
// made it has moved on or returned. It is verified once where it is made,
// against the contract of the type it is given, as a function of its own:
// its parameters are what the contract allows, the memory it sees is
// memory of its own, and of the variables it captures it knows this:
//
//   - one that nothing assigns but its declaration, and whose address is not
//     taken, has the value it has where the literal is made, for ever, with
//     what is known of that value there;
//   - any other is a value of its type and nothing more.
//
// It may not assign a variable it captures, so no call through a value can
// change a variable of any function, and what in-place literals assume of
// the variables they capture stays true. A loop variable belongs to its
// iteration from Go 1.22 on and is captured with the value it has there; in
// older files the iterations share it, and it is assigned by the loop.

// madeLiteral checks a function literal that is made into a value of a
// function type with the contract T.
func (v *fnVerifier) madeLiteral(lit *ast.FuncLit, T *funcInfo, st *state, guard []*logic.Term) {
	captured := v.capturedBy(lit)
	v.stratified(lit)
	sig := v.info.TypeOf(lit).(*types.Signature)
	fn := &funcInfo{
		obj:         types.NewFunc(lit.Pos(), v.pass.Pkg, T.obj.Name(), sig),
		requires:    T.requires,
		ensures:     T.ensures,
		modifies:    T.modifies,
		params:      slices.Collect(sig.Params().Variables()),
		results:     slices.Collect(sig.Results().Variables()),
		paramNames:  map[string]*types.Var{},
		resultNames: map[string]int{},
		runs:        map[*types.Var]bool{},
		vouches:     map[int]bool{},
		decl:        &ast.FuncDecl{Name: &ast.Ident{NamePos: lit.Pos(), Name: T.obj.Name()}, Type: lit.Type, Body: lit.Body},
		ownParams:   map[string]*types.Var{},
	}
	// The contract names the parameters and results of the type, which are
	// those of the literal in the same order.
	for i, param := range T.params {
		fn.paramNames[param.Name()] = fn.params[i]
	}
	for name, index := range T.resultNames {
		fn.resultNames[name] = index
	}
	for _, param := range fn.params {
		fn.ownParams[param.Name()] = param
	}
	for _, c := range v.fn.body {
		if c.pos >= lit.Body.Pos() && c.pos < lit.Body.End() {
			fn.body = append(fn.body, c)
		}
	}
	site := v.site(lit.Pos(), "in the function literal used as a value of type %s at %s", T.obj.Name(), v.placeOf(lit.Pos()))
	sv, entry, carry := v.subVerifier(fn, st, guard, site)
	for _, variable := range captured {
		held := st.vals[variable]
		if held == nil {
			continue
		}
		if v.final(variable) || v.boxed[variable] {
			// The value is fixed: the variable itself, or for one that
			// lives in memory, the pointer to it. What it holds there is
			// read from the memory the literal sees.
			entry.vals[variable] = carry.value(held)
			continue
		}
		entry.vals[variable] = sv.unknown(variable.Name(), variable.Type(), entry)
	}
	sv.looped = findLooped(lit.Body)
	sv.classifyLiterals()
	for _, variable := range slices.Concat(fn.params, fn.results) {
		if sv.boxed[variable] && entry.vals[variable] != nil {
			sv.bind(entry, variable, entry.vals[variable])
		}
	}
	sv.seq(lit.Body.List, lit.Body.Lbrace, lit.Body.Rbrace, entry, ctrl{}, func(end *state) {
		sv.returned(end, nil, lit.Body.Rbrace)
	})
}

// capturedBy returns the local variables declared outside a literal that it
// uses, and refuses one that it assigns, or that holds a literal used in
// place: that literal may assign the variables of the function around it.
func (v *fnVerifier) capturedBy(lit *ast.FuncLit) []*types.Var {
	outside := func(variable *types.Var) bool {
		return variable != nil && !variable.IsField() && variable.Pkg() == v.pass.Pkg && variable.Parent() != v.pass.Pkg.Scope() &&
			(variable.Pos() < lit.Pos() || variable.Pos() >= lit.End())
	}
	var captured []*types.Var
	seen := map[*types.Var]bool{}
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		var targets []ast.Expr
		switch n := n.(type) {
		case *ast.Ident:
			variable, _ := v.info.Uses[n].(*types.Var)
			if !outside(variable) || seen[variable] {
				break
			}
			seen[variable] = true
			if v.boundLits[variable] != nil {
				v.unsupported(n.Pos(), fmt.Sprintf("a function literal used as a value cannot use %s, which holds a function literal "+
					"of the function around it", n.Name))
			}
			captured = append(captured, variable)
		case *ast.AssignStmt:
			targets = n.Lhs
		case *ast.IncDecStmt:
			targets = []ast.Expr{n.X}
		case *ast.RangeStmt:
			if n.Tok == token.ASSIGN {
				targets = []ast.Expr{n.Key, n.Value}
			}
		}
		for _, target := range targets {
			if variable := v.assignedLocal(target); outside(variable) && !v.boxed[variable] {
				v.unsupported(target.Pos(), fmt.Sprintf("a function literal used as a value cannot assign %s, a variable of the function "+
					"around it: it may run when that function has moved on, and no call of it could tell that function what it did", variable.Name()))
			}
		}
		return true
	})
	return captured
}

// final reports whether a variable keeps the value it is declared with: no
// statement of the declared function around it assigns it but its
// declaration, its address is not taken, and it is not a named result, which
// a return assigns. The variable of a range loop belongs to its iteration
// from Go 1.22 on; before that the loop assigns it at each iteration.
func (v *fnVerifier) final(variable *types.Var) bool {
	body := v.bodyOrigin()
	if v.assignedIn == nil {
		v.assignedIn = map[*ast.BlockStmt]map[*types.Var]bool{}
	}
	assigned := v.assignedIn[body]
	if assigned == nil {
		assigned = v.findReassigned(body)
		v.assignedIn[body] = assigned
	}
	return !assigned[variable] && !v.boxed[variable]
}

// findReassigned returns the variables of a body that something other than
// their declaration assigns.
func (v *fnVerifier) findReassigned(body *ast.BlockStmt) map[*types.Var]bool {
	assigned := map[*types.Var]bool{}
	mark := func(e ast.Expr) {
		if variable := v.assignedLocal(e); variable != nil {
			assigned[variable] = true
		}
	}
	results := func(t *ast.FuncType) {
		if t.Results == nil {
			return
		}
		for _, field := range t.Results.List {
			for _, name := range field.Names {
				if variable, ok := v.info.Defs[name].(*types.Var); ok {
					assigned[variable] = true
				}
			}
		}
	}
	// The named results of the declared function whose body this is, which
	// may be the function around a literal that is verified on its own.
	for _, fn := range v.order {
		if fn.decl.Body == body {
			results(fn.decl.Type)
		}
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			results(n.Type)
		case *ast.AssignStmt:
			for _, lhs := range n.Lhs {
				id, isIdent := ast.Unparen(lhs).(*ast.Ident)
				if n.Tok == token.DEFINE && isIdent && v.info.Defs[id] != nil {
					continue
				}
				mark(lhs)
			}
		case *ast.IncDecStmt:
			mark(n.X)
		case *ast.RangeStmt:
			if n.Tok == token.ASSIGN || !v.freshEachIteration(n.Pos()) {
				for _, target := range []ast.Expr{n.Key, n.Value} {
					if target != nil {
						mark(target)
					}
				}
			}
		}
		return true
	})
	return assigned
}

// stratified refuses a literal used as a value whose body may call through
// a function value: itself, in a literal it calls in place, or in what it
// calls. No contract of a function type has a variant, so nothing would
// prove that a chain of such calls ends. A literal that it makes into a
// value is checked where it is made.
func (v *fnVerifier) stratified(lit *ast.FuncLit) {
	bound, _ := literalUses(v.info, lit.Body)
	inPlace := map[*ast.FuncLit]bool{}
	for _, inner := range bound {
		inPlace[inner] = true
	}
	refuse := func(pos token.Pos, what string) {
		v.unsupported(pos, fmt.Sprintf("the function literal used as a value %s, and code that a function value runs cannot do that yet: "+
			"no contract of a function type has a variant, so nothing would prove that such calls end", what))
	}
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			return inPlace[n]
		case *ast.RangeStmt:
			if rangesByCalling(v.info.TypeOf(n.X)) {
				refuse(n.Pos(), "ranges over a function")
			}
		case *ast.CallExpr:
			tv := v.info.Types[n.Fun]
			if tv.IsType() || tv.IsBuiltin() {
				break
			}
			if callee := typeutil.StaticCallee(v.info, n); callee != nil {
				if v.pkgVerifier.mayCallValues(callee) {
					refuse(n.Pos(), fmt.Sprintf("calls %s, which may call through a function value", callee.Name()))
				}
				// What a trusted function is handed to call runs during the
				// call, as part of the literal.
				for _, arg := range v.pkgVerifier.handedArgs(n) {
					switch handed, isLit := v.pkgVerifier.handedFunc(arg); {
					case isLit:
						inPlace[ast.Unparen(arg).(*ast.FuncLit)] = true
					case handed != nil:
						if v.pkgVerifier.mayCallValues(handed) {
							refuse(arg.Pos(), fmt.Sprintf("hands %s to %s, which calls it, and %s may call through a function value",
								handed.Name(), callee.Name(), handed.Name()))
						}
					default:
						refuse(arg.Pos(), fmt.Sprintf("hands the function value %s to %s, which calls it", types.ExprString(arg), callee.Name()))
					}
				}
				break
			}
			switch fun := ast.Unparen(n.Fun).(type) {
			case *ast.FuncLit:
				inPlace[fun] = true
				return true
			case *ast.Ident:
				if variable, ok := v.info.Uses[fun].(*types.Var); ok && bound[variable] != nil {
					return true
				}
			}
			if callee, _ := typeutil.Callee(v.info, n).(*types.Func); isIfaceMethod(callee) {
				refuse(n.Pos(), "calls through the interface value "+types.ExprString(ast.Unparen(n.Fun).(*ast.SelectorExpr).X))
				break
			}
			refuse(n.Pos(), "calls through the function value "+types.ExprString(n.Fun))
		}
		return true
	})
}
