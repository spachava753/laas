package vego

import (
	"cmp"
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// A trusted function may take a function and call it while it runs, as
// sort.Search and strings.IndexFunc do. Its entry can give such a parameter
// a contract under calls, which names the parameters of the function type
// and says what holds whenever the trusted function calls it:
//
//	sort.Search:
//	  runs: [f]
//	  calls:
//	    f(i):
//	      requires: ["0 <= i < n"]
//
// The parameter must be listed under runs as well: the entry claims what
// runs claims, that the function calls f only before it returns, on the
// goroutine that called it, and holds it nowhere it was not held before the
// call, and also that it calls f
// only with arguments that meet the requires of calls, in the state at that
// call. The rest of the contract has to hold for every function that meets
// them, returns, and writes nothing that the modifies of the entry covers.

// callback is the contract a trusted entry gives one function parameter.
type callback struct {
	// param is the parameter of the trusted function, and sig its function
	// type.
	param *types.Var
	sig   *types.Signature
	// params are the parameters of the function type, named as the entry
	// names them.
	params []*types.Var
	// fn resolves the requires: it names the parameters of the function
	// type and those of the trusted function.
	fn       *funcInfo
	requires []*clause
	// applied is set when the ensures of the entry speak of what the
	// function returns, and deterministic when the entry relies on it
	// returning the same result for the same arguments, which applying it
	// does too.
	applied       bool
	deterministic bool
	// source is set for a contract under Calls of a verified function,
	// whose body is verified against it; see sourcecalls.go.
	source bool
}

// callWords are the names that a formula reads as something else when
// they are applied, as in is(err, target).
var callWords = logic.Reserved

// trustedCall reads one entry under calls of a trusted contract into fn,
// or records why it cannot be used.
func (pv *pkgVerifier) trustedCall(fn *funcInfo, item trustCall) {
	param, ok := fn.paramNames[item.name]
	if !ok {
		fn.defect("its calls %s(...): %s is not a parameter", item.name, item.name)
		return
	}
	sig, isFunc := param.Type().Underlying().(*types.Signature)
	switch {
	case !isFunc:
		fn.defect("its calls lists %s, whose type %s is not a function type", item.name, param.Type())
		return
	case !fn.runs.get(param):
		fn.defect("its calls gives %s a contract, so its runs must list %s too: calls claims everything runs does", item.name, item.name)
		return
	case fn.calls.get(param) != nil:
		fn.defect("its calls lists %s twice", item.name)
		return
	case pv.valueContract(param.Type()) != nil:
		fn.defect("its calls gives %s a contract, but its type %s has a contract of its own", item.name, param.Type())
		return
	case sig.TypeParams() != nil:
		fn.defect("its calls lists %s, whose type %s is generic, which is not supported yet", item.name, param.Type())
		return
	case slices.Contains(callWords, item.name):
		fn.defect("its calls lists %s, which a formula reads as a word of its own when it is applied", item.name)
		return
	case len(item.params) != sig.Params().Len():
		fn.defect("its calls names %d parameters for %s, whose type %s has %d", len(item.params), item.name, param.Type(), sig.Params().Len())
		return
	}
	pos := pv.trustPos(fn.trust.file, item.line, item.col)
	// The requires name the parameters of the function type, and those of
	// the trusted function, whose values are those of the call.
	cb := &callback{param: param, sig: sig}
	cb.fn = &funcInfo{
		obj: fn.obj, trust: fn.trust, paramNames: map[string]*types.Var{}, resultNames: map[string]int{},
		vouches: map[int]bool{},
		genericTypes: fn.genericTypes,
	}
	for name, p := range fn.paramNames {
		cb.fn.paramNames[name] = p
	}
	for i, name := range item.params {
		// A formula must read the name as a name, and not as a word of its
		// own such as True, or as a result, result1, result2, ...
		node, err := logic.ParseFormula(name)
		rest, numbered := strings.CutPrefix(name, "result")
		numbered = numbered && strings.Trim(rest, "0123456789") == ""
		readAsName := err == nil && node.Kind == logic.NIdent && node.Name == name && !numbered
		switch {
		case slices.Contains(item.params[:i], name):
			fn.defect("its calls names the parameter %s of %s twice", name, item.name)
			return
		case fn.paramNames[name] != nil:
			fn.defect("its calls names a parameter of %s %s, which is a parameter of %s already", item.name, name, fn.obj.Name())
			return
		case !readAsName || slices.Contains(callWords, name):
			fn.defect("its calls names a parameter of %s %s, which means something else in a formula", item.name, name)
			return
		}
		if _, isResult := fn.resultNames[name]; isResult {
			fn.defect("its calls names a parameter of %s %s, which is a result of %s", item.name, name, fn.obj.Name())
			return
		}
		named := types.NewVar(pos, fn.obj.Pkg(), name, sig.Params().At(i).Type())
		// What the parameter is in the generic signature, for a contract
		// of an instantiation.
		if t := fn.genericTypes[param]; t != nil {
			if generic, ok := t.Underlying().(*types.Signature); ok {
				fn.genericTypes[named] = generic.Params().At(i).Type()
			}
		}
		cb.params = append(cb.params, named)
		cb.fn.params = append(cb.fn.params, named)
		cb.fn.paramNames[name] = named
	}
	cb.fn.params = append(cb.fn.params, fn.params...)
	// What the trusted function passes to the callback, and what it gets
	// back, must be values vego models. Code there would be code handed on
	// between two functions vego does not see.
	for _, tuple := range []*types.Tuple{sig.Params(), sig.Results()} {
		for variable := range tuple.Variables() {
			if _, modelled := layoutOf(variable.Type()); !modelled {
				fn.typeDefect("its calls lists %s, whose type %s takes or returns a %s, which is not supported", item.name, param.Type(), variable.Type())
				return
			}
			if holdsCode(variable.Type(), map[types.Type]bool{}) {
				fn.typeDefect("its calls lists %s, whose type %s takes or returns a %s, which can hold code; that is not supported yet",
					item.name, param.Type(), variable.Type())
				return
			}
		}
	}
	compares := len(item.requires)
	for i, formula := range slices.Concat(item.requires, item.compares) {
		// The requires are read in the state at each call of the function
		// parameter, and old(p) of a parameter p of the trusted function
		// reads p in the state at the call of the trusted function. old of
		// anything else has no meaning there.
		if name := oldOfOther(formula.node, fn, cb.params); name != "" {
			fn.defect("its calls requires %q for %s uses old(%s), which has no meaning there: in a requires under calls, old names only a parameter of %s, "+
				"read as it was when %s was called", formula.text, item.name, name, fn.obj.Name(), fn.obj.Name())
			return
		}
		cb.requires = append(cb.requires, &clause{
			kind: "requires", text: formula.text, node: formula.node, res: pv.plain,
			pos:      pv.trustPos(fn.trust.file, formula.line, formula.col),
			compares: i >= compares,
		})
	}
	cb.fn.requires = cb.requires
	// The ensures of the entry, and only those, may apply the function: a
	// requires is read before the function has been called.
	// The contract is kept when it has a defect here, so that what applies
	// it is read as an application and draws a message that says so.
	for _, c := range fn.requires {
		if applies(c.node, item.name) {
			fn.defect("its requires %q applies %s; only its ensures can speak of what %s returns", c.text, item.name, item.name)
			cb.applied = true
		}
	}
	for _, c := range fn.ensures {
		cb.applied = cb.applied || applies(c.node, item.name)
	}
	if cb.applied && !applicable(sig) {
		fn.typeDefect("its ensures applies %s, whose type %s does not have one integer parameter and one integer or boolean result, "+
			"which is all that can be applied yet", item.name, param.Type())
	}
	if item.deterministic && sig.Results().Len() == 0 {
		fn.defect("its calls says that %s is deterministic, but %s returns nothing", item.name, item.name)
	}
	cb.deterministic = item.deterministic || cb.applied
	fn.calls.set(param, cb)
}

// applies reports whether a formula applies a name, as in f(i).
func applies(n *logic.Node, name string) bool {
	found := false
	n.Walk(func(n *logic.Node) {
		found = found || (n.Kind == logic.NCall && n.Name == name)
	})
	return found
}

// applicable reports whether what a function of the type returns can be
// stated in a formula: it takes one integer, and returns one integer or
// boolean.
func applicable(sig *types.Signature) bool {
	if sig.Params().Len() != 1 || sig.Results().Len() != 1 {
		return false
	}
	param, _ := sig.Params().At(0).Type().Underlying().(*types.Basic)
	result, _ := sig.Results().At(0).Type().Underlying().(*types.Basic)
	return param != nil && param.Info()&types.IsInteger != 0 && result != nil && result.Info()&(types.IsInteger|types.IsBoolean) != 0
}

// mentionsMemory reports whether a term reads a region of memory as it is
// on entry.
func mentionsMemory(t *logic.Term) bool {
	if t.Op == logic.OpConst && strings.HasPrefix(t.Name, entryRegion) {
		return true
	}
	return slices.ContainsFunc(t.Args, mentionsMemory)
}

// oldOfOther returns the root of the first old(...) in a formula that is
// not a parameter of fn, or one of the parameters of the function type,
// which are values of the call of the function parameter; or "".
func oldOfOther(n *logic.Node, fn *funcInfo, own []*types.Var) string {
	found := ""
	n.Walk(func(n *logic.Node) {
		if found != "" || n.Kind != logic.NCall || n.Name != "old" || len(n.Kids) != 1 {
			return
		}
		root := n.Kids[0]
		for len(root.Kids) > 0 && root.Kind != logic.NIdent {
			root = root.Kids[0]
		}
		param := fn.paramNames[root.Name]
		if root.Kind != logic.NIdent || param == nil || slices.Contains(own, param) {
			found = cmp.Or(root.Name, "...")
		}
	})
	return found
}

// callRequires resolves what holds when a trusted function calls a
// function parameter: in memory as it is at that call, with the arguments
// of that call for the parameters of the function type and those of the
// call of the trusted function for its own, and old(p) of a parameter p
// of the trusted function in memory as it was at the call of the trusted
// function, atCall. A clause under compares says nothing at an
// instantiation where a formula cannot compare what it compares.
func (v *fnVerifier) callRequires(cb *callback, given []value, args map[*types.Var]value, st *state, atCall memory) []*logic.Term {
	all := map[*types.Var]value{}
	for param, val := range args {
		all[param] = val
	}
	own := map[*types.Var]bool{}
	for i, param := range cb.params {
		all[param] = given[i]
		own[param] = true
	}
	env := &specEnv{v: v, sink: st, fn: cb.fn, args: all, now: st.mem, oldMem: atCall, notOld: own}
	var facts []*logic.Term
	for _, c := range cb.requires {
		if !c.compares {
			facts = append(facts, v.formula(c, c.node, env))
			continue
		}
		t, err := v.resolverOf(c).Formula(c.node, env)
		switch {
		case errors.Is(err, errIncomparable) || errors.As(err, new(*logic.IncomparableError)):
			continue
		case err != nil:
			v.misread(c, err)
		}
		v.noteIs(st, t)
		facts = append(facts, t)
	}
	return facts
}

// forbidden is what a trusted function may write while it runs a function
// it was handed, which that function may not write: the two writes would
// meet in memory whose contents nobody describes. A run of what o.Do is
// handed that calls o.Do writes o, and never returns.
type forbidden struct {
	targets []target
	by      string
	// direct is set for the allocations that the other arguments of a
	// function with Calls refer to directly, which its runs may not write
	// either; see sourcecalls.go.
	direct bool
}

// callHanding verifies a call of a trusted function that is handed a
// function it calls while it runs. The other arguments are evaluated as
// for any call. On one branch of && or || the call is made in a state of
// its own, which is joined with the one where it is not made, as a call of
// a function literal is.
func (v *fnVerifier) callHanding(call *ast.CallExpr, fn *funcInfo, st *state, guard []*logic.Term, operands *ceiling) []value {
	callee := fn.obj
	sig := callee.Type().(*types.Signature)
	handed := map[*types.Var]*handOver{}
	args := map[*types.Var]value{}
	if sig.Recv() != nil {
		args[sig.Recv()] = v.receiver(call, sig.Recv(), st, guard)
	}
	for _, passed := range v.bindCall(call, sig) {
		param := passed.param
		if fn.calls.get(param) != nil {
			// A parameter under calls has a function type, which is never
			// variadic, so it is given one argument.
			handed[param] = v.handOver(fn, param, passed.expr, st, guard)
			// A function value is one reference, and this one is not nil.
			args[param] = value{logic.RefLit(1)}
			continue
		}
		args[param] = v.evalPassed(passed, st, guard)
	}
	u := v.unit
	u.reach(operands)
	// The versions of the unit are recorded here, from the state the
	// joined call leaves; see order.go.
	before := v.snapshot(st)
	v.unit = nil
	defer func() { v.unit = u }()
	v.handing = handed
	results := func(at *state) []value {
		return v.invoke(call, fn, args, at, nil)
	}
	var out []value
	if len(guard) == 0 {
		out = results(st)
	} else {
		ran := st.clone()
		ran.assume(logic.And(guard...))
		made := results(ran)
		skipped := st.clone()
		skipped.assume(logic.Not(logic.And(guard...)))
		zero := make([]value, sig.Results().Len())
		for i := range zero {
			zero[i] = zeroValue(sig.Results().At(i).Type())
		}
		out = v.join(st, []litEnd{{ran, made}, {skipped, zero}}, sig)
	}
	v.unit = u
	if changed(before, v.snapshot(st)) {
		u.wrote(st, "the call to "+callee.Name())
	}
	return out
}

// runHanded runs, within the call of a trusted function, the functions it
// was handed, once each in a state that stands for every state in which
// the trusted function may call them, and leaves in st what is known once
// the call has returned. written is what the trusted function may write,
// which st has forgotten already.
//
// A handed function may run any number of times, never included, in any
// order with the others and with the writes of the trusted function. So in
// the state of a run, as at the head of a loop without an invariant, what
// any of them or the trusted function may write is forgotten, and the rest
// is as it was at the call; its arguments are what the contract under calls
// says of them. What the handed functions write is forgotten once more
// after the call. A run is held to everything the caller is held to, since
// it runs as part of the call, and it may not write what the trusted
// function may.
//
// atCall is the state at the call, before anything is forgotten, from which
// the state of each run is made, and callMark the number of names made
// before the call. A run that the trusted function relies on to return the
// same result for the same argument is summarised; see summary.
func (v *fnVerifier) runHanded(call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value, written []target, atCall, st *state, callMark int) map[*types.Var]*logic.Term {
	handed := v.handing
	v.handing = nil
	if handed == nil {
		panic("vego: internal error: a call of a trusted function that calls what it is given was applied without it")
	}
	var bodies []ast.Node
	for _, param := range fn.params {
		if h := handed[param]; h != nil && h.lit != nil {
			bodies = append(bodies, h.lit.Body)
		}
	}
	eff := v.effects(bodies...)
	for _, param := range fn.params {
		if h := handed[param]; h != nil && h.lit == nil {
			v.handedSites(h.arg, h.contract, eff)
		}
	}
	name := types.ExprString(call.Fun)
	// The invariant of the runs holds at the call and after what the callee
	// writes between two runs; see handinv.go. One that is not proved there
	// gives the runs no summary, which would rest on it.
	invariants := v.handInvariants[call]
	invariantsFailed := false
	if invariants != nil {
		before := v.reports
		v.invariantHolds(invariants, atCall.clone(), "invariant may not hold where "+name+" is called")
		v.keptBetweenRuns(invariants, atCall, written, eff, name)
		invariantsFailed = v.reports > before
	}
	var summaries []*logic.Term
	applied := map[*types.Var]*logic.Term{}
	runsMade := map[string]bool{}
	stKnown := len(st.hyps)
	for _, param := range fn.params {
		h, cb := handed[param], fn.calls.get(param)
		if h == nil {
			continue
		}
		// Everything made from here on stands for the state of a run or
		// for what the run made, apart from the arguments.
		mark, known := len(v.made), len(atCall.hyps)
		reportsBefore := v.reports
		// The state of a run stands for the state at the call and every
		// state between two runs: the trusted function may have written its
		// part of memory before any run, or between two runs, and the runs
		// what they write. It says nothing of memory at references from the
		// bound at the call on, so it also stands for a state in which the
		// trusted function has created and written objects of its own. A
		// change that states facts about memory not yet allocated breaks
		// that, and with it the summary of a run.
		head := atCall.clone()
		for _, t := range written {
			v.havoc(head, t, nil)
		}
		head = v.forget(head, eff)
		v.assumeInvariant(invariants, head)
		start := len(head.hyps)
		given := make([]value, len(cb.params))
		for i, p := range cb.params {
			given[i] = v.unknown(p.Name(), p.Type(), head)
		}
		for _, fact := range v.callRequires(cb, given, args, head, atCall.mem) {
			head.assume(fact)
		}
		// What the arguments of a run are known to be: their types and the
		// requires of calls, which for a function the entry applies speak
		// of values of the call only.
		premise := slices.Clip(head.hyps[start:])
		v.forbidden = append(v.forbidden, forbidden{targets: written, by: name})
		pushed := 1
		if cb.source {
			v.forbidden = append(v.forbidden, forbidden{targets: v.directTargets(fn, args), by: name, direct: true})
			pushed++
		}
		var results []value
		what := "the function literal"
		if h.lit != nil {
			results = v.inline(h.lit, given, head, nil, v.site(h.lit.Pos(), "in the function literal run by %s at %s", name, v.placeOf(h.lit.Pos())))
		} else {
			results = v.runHandedCall(h, cb, given, head, name)
			what = types.ExprString(h.arg)
			if h.value {
				what = "the function value " + what
			}
		}
		v.forbidden = v.forbidden[:len(v.forbidden)-pushed]
		// The state the run leaves is the join of its returns, after its
		// own deferred calls.
		v.invariantHolds(invariants, head, "invariant may not be kept by "+what+" run by "+name)
		// The facts of the run are taken once, and both the proof that the
		// run returns the same result for the same argument and the summary
		// are made from them.
		run := ranOnce{head: head, facts: slices.Clip(head.hyps[known:]), made: slices.Clip(v.made[mark:]),
			given: given, premise: premise, results: results}
		for name := range run.produced() {
			runsMade[name] = true
		}
		// A run that met a report went on past an obligation that failed by
		// assuming it, which may be false of every run, so what the run
		// gives the caller would rest on it: its summary is left out, which
		// only weakens what the caller knows. The run's report stands.
		if !cb.deterministic || v.reports > reportsBefore || invariantsFailed {
			continue
		}
		v.checkRunNames(run, callMark)
		if !v.sameEachRun(run, h.arg.Pos(), what, name) || !cb.applied {
			continue
		}
		sort, _ := sortOf(cb.sig.Results().At(0).Type())
		applied[param] = v.fresh("returns of "+param.Name(), logic.SeqOf(sort))
		summaries = append(summaries, v.summary(run, applied[param]))
	}
	*st = *v.forget(st, eff)
	v.assumeInvariant(invariants, st)
	// A summary is true in every state that meets the facts at the call,
	// so it cannot make a state contradictory that was not. If it does,
	// the summary is wrong, and anything would follow from it; that must
	// not pass quietly.
	live := len(summaries) > 0 && !v.quickly(st, nil, logic.False())
	for _, summary := range summaries {
		st.assume(summary)
	}
	if live && v.quickly(st, nil, logic.False()) {
		panic("vego: internal error: what is known of the functions handed to " + name + " contradicts what is known at the call")
	}
	// A fact about what a run made, outside the existential of a summary,
	// would be a fact about one hypothetical run, which another could
	// contradict.
	for _, fact := range st.hyps[stKnown:] {
		if _, mentioned := estranged(fact, runsMade); mentioned {
			panic("vego: internal error: a fact about what a run of a function handed to a trusted function made reached the state after the call")
		}
	}
	return applied
}

// checkRunNames panics unless every constant that the facts or the result
// of a run mention is an argument of the run, was made for the run, or was
// made before the call: the summary is a statement about the state at the
// call, and anything else in it would be free where it must be bound.
func (v *fnVerifier) checkRunNames(run ranOnce, callMark int) {
	before := map[string]bool{}
	for _, name := range v.made[:callMark] {
		before[name] = true
	}
	since := map[string]bool{}
	for _, name := range v.made[callMark:] {
		since[name] = true
	}
	produced := run.produced()
	allowed := func(name string) bool {
		return before[name] || produced[name] || !since[name] || slices.ContainsFunc(run.given, func(arg value) bool {
			return slices.ContainsFunc(arg, func(leaf *logic.Term) bool { return leaf.Name == name })
		})
	}
	seen := map[*logic.Term]bool{}
	var visit func(t *logic.Term)
	visit = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		if t.Op == logic.OpConst && !allowed(t.Name) {
			panic("vego: internal error: the run of a function handed to a trusted function mentions " + t.Name +
				", which was made for the call but not for the run")
		}
		for _, arg := range t.Args {
			visit(arg)
		}
	}
	for _, fact := range run.facts {
		visit(fact)
	}
	for _, result := range run.results {
		for _, leaf := range result {
			visit(leaf)
		}
	}
}

// ranOnce is the run of a function handed over that a trusted function
// relies on to give the same result for the same argument: the state the
// run ended in, the facts it added to those known at the call, the names
// made for the state of the run and by the run, the arguments, what was
// known of them, and the results.
type ranOnce struct {
	head    *state
	facts   []*logic.Term
	made    []string
	given   []value
	premise []*logic.Term
	results []value
}

// produced returns the names a run made, apart from its arguments: the
// state it ran in, and what it made.
func (run ranOnce) produced() map[string]bool {
	names := map[string]bool{}
	for _, name := range run.made {
		names[name] = true
	}
	for _, arg := range run.given {
		for _, leaf := range arg {
			delete(names, leaf.Name)
		}
	}
	return names
}

// sameEachRun proves that the result of a run is fixed by its argument:
// for a second run with the same argument, whose state and whatever it
// made are named apart, the result is the same. The state of a run stands
// for every state in which the trusted function may call the function, so
// this covers runs between writes of the trusted function and of earlier
// runs. It reports when the proof fails.
func (v *fnVerifier) sameEachRun(run ranOnce, pos token.Pos, what, by string) bool {
	names := run.produced()
	memo := map[*logic.Term]*logic.Term{}
	rename := func(t *logic.Term) *logic.Term {
		return renamedApart(t, names, memo)
	}
	twice := run.head.clone()
	for _, fact := range run.facts {
		twice.assume(rename(fact))
	}
	var same []*logic.Term
	for _, result := range run.results {
		for _, leaf := range result {
			other := rename(leaf)
			if leaf.Sort == logic.Bool {
				same = append(same, logic.Iff(leaf, other))
			} else {
				same = append(same, v.same(leaf, other))
			}
		}
	}
	if result := v.attempt(twice, nil, logic.And(same...)); result != solver.Proved {
		v.report(pos, "%s run by %s is not proved to return the same result whenever it is called with the same argument, "+
			"which the trusted contract of %s relies on%s", what, by, by, limitNote(result))
		return false
	}
	return true
}

// renamedApart returns a term in which every constant of the given names
// is replaced by one of its own, the same for each name. The names the
// verifier makes end in a number, so no name with " again" after it is
// one of them.
func renamedApart(t *logic.Term, names map[string]bool, memo map[*logic.Term]*logic.Term) *logic.Term {
	if done, ok := memo[t]; ok {
		return done
	}
	result := t
	switch {
	case t.Op == logic.OpConst && names[t.Name]:
		result = logic.Const(t.Name+" again", t.Sort)
	case len(t.Args) > 0:
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = renamedApart(arg, names, memo)
			changed = changed || args[i] != arg
		}
		if changed {
			result = logic.WithArgs(t, args)
		}
	}
	memo[t] = result
	return result
}

// summary states what a function that a trusted function applies returns
// for each argument: for every k that its type and the requires of calls
// allow, some run with the argument k, in some state of a run, has the
// facts this run has, and returns returns[k]. Such a run exists for every
// such k, since the state at the call is a state of a run and the body was
// verified for every argument the premise allows; and since every run
// returns the same result for the same argument, returns[k] is what each
// call of the trusted function got.
func (v *fnVerifier) summary(run ranOnce, returns *logic.Term) *logic.Term {
	names := run.produced()
	var made []string
	for _, name := range run.made {
		if names[name] {
			made = append(made, name)
		}
	}
	facts := slices.Clone(run.facts)
	// An applied function has one result of a single leaf.
	result := run.results[0][0]
	got := logic.Select(returns, run.given[0][0])
	if result.Sort == logic.Bool {
		facts = append(facts, logic.Iff(got, result))
	} else {
		facts = append(facts, logic.Eq(got, result))
	}
	some := v.someOutcome(facts, made)
	k := v.bound("k")
	by := map[string]*logic.Term{run.given[0][0].Name: k}
	premise := substituteConsts(logic.And(run.premise...), by, map[*logic.Term]*logic.Term{})
	return logic.Forall(k, logic.Implies(premise, substituteConsts(some, by, map[*logic.Term]*logic.Term{})))
}

// checkNotForbidden requires that a write made by a function that a
// trusted function runs misses everything that trusted function may write
// itself, whether or not the memory was created since the caller was
// entered.
func (v *fnVerifier) checkNotForbidden(st *state, guard []*logic.Term, w written, pos token.Pos, what string) {
	for _, f := range v.forbidden {
		var apart []*logic.Term
		for _, t := range f.targets {
			apart = append(apart, outside(w, t))
		}
		goal := logic.And(apart...)
		if result := v.attempt(st, guard, goal); result != solver.Proved && f.direct {
			v.report(pos, "%s, which may be what an argument of %s refers to directly; a function %s calls under Calls may not write "+
				"the elements of a slice from its first to its capacity, the struct a pointer points to, or a map that %s is handed beside it%s", what, f.by, f.by, f.by, limitNote(result))
			st.assume(logic.Implies(logic.And(guard...), goal))
		} else if result != solver.Proved {
			v.report(pos, "%s, which %s may write itself while it runs the function it is handed; "+
				"a function it is handed may not write what it may write%s", what, f.by, limitNote(result))
			st.assume(logic.Implies(logic.And(guard...), goal))
		}
	}
}

// outside states that a write misses a target: the two lie in different
// allocations, or in stretches of one allocation that do not meet, in each
// region they share. A target through a nil pointer covers nothing.
func outside(w written, t target) *logic.Term {
	var apart []*logic.Term
	for _, part := range w.parts {
		for _, c := range t.stretches() {
			switch {
			case c.key != part.key:
			case c.lo == nil || part.lo == nil:
				apart = append(apart, logic.Ne(w.ref, t.ref))
			default:
				apart = append(apart, logic.Or(logic.Ne(w.ref, t.ref), logic.Le(part.hi, c.lo), logic.Le(c.hi, part.lo)))
			}
		}
	}
	return logic.Or(logic.Eq(t.ref, logic.RefLit(0)), logic.And(apart...))
}

// handedArgs returns the arguments of a call that its callee, a trusted
// function, is handed to call while it runs: those for its parameters with
// a contract under calls.
func (pv *pkgVerifier) handedArgs(call *ast.CallExpr) []ast.Expr {
	callee := pv.staticCalleeAt(call)
	if callee == nil || isGeneric(callee) || isGeneric(callee.Origin()) {
		return nil
	}
	fn := pv.trustedContract(callee.Origin())
	if own := pv.sourceCallsOf(callee); own != nil {
		fn = own
	}
	if fn == nil || fn.calls.len() == 0 {
		return nil
	}
	sig := callee.Type().(*types.Signature)
	bound, _ := bindArgs(pv.info, call, paramsOf(sig), sig.Variadic())
	var handed []ast.Expr
	for _, b := range bound {
		if !b.packed && fn.calls.get(b.param) != nil {
			handed = append(handed, b.expr)
		}
	}
	return handed
}

// callsParam reports whether a variable is a parameter of a function that
// its trusted contract, as written, gives a contract under calls. It reads
// the entry without checking it: an entry with a defect cannot be used, so
// nothing relies on what this says of it.
func (pv *pkgVerifier) callsParam(fn *funcInfo, variable *types.Var) bool {
	key := fn.obj.FullName()
	var entry *trustEntry
	if pv.projectTrust != nil {
		entry = pv.projectTrust.entries[key]
	}
	for _, file := range shippedContracts() {
		if entry == nil {
			entry = file.entries[key]
		}
	}
	if entry == nil || variable.Parent() != fn.obj.Scope() {
		return false
	}
	return slices.ContainsFunc(entry.calls, func(call trustCall) bool { return call.name == variable.Name() })
}

// handOver is what a call hands a trusted function to call while it runs:
// a function literal written there, or a function, a method value, or a
// value of a function type with a contract. Each of the last three is run
// as a call the caller makes, of the contract of the function, or of the
// type of the value; the receiver of a method value and the value are
// evaluated where they are handed over.
type handOver struct {
	arg      ast.Expr
	lit      *ast.FuncLit
	contract *funcInfo
	// recv is the receiver of a method value, and value is set for a value
	// of a function type.
	recv  value
	value bool
}

// handOver evaluates what an argument hands a trusted function to call, or
// refuses what cannot be handed over: anything whose code nothing
// describes.
func (v *fnVerifier) handOver(fn *funcInfo, param *types.Var, arg ast.Expr, st *state, guard []*logic.Term) *handOver {
	inner := ast.Unparen(arg)
	if lit, ok := inner.(*ast.FuncLit); ok {
		return &handOver{arg: arg, lit: lit}
	}
	named, method := v.valueForm(inner)
	callee := named
	if method != nil {
		callee = method
	}
	// What a function with Calls hands f, code that nobody has seen may run
	// when f is a value from outside, or trusted (F4 of the design review
	// of F40); whose origin it has is not known where f is handed over.
	carriesCode := func(what string) {
		cb := fn.calls.get(param)
		if cb == nil || !cb.source {
			return
		}
		for variable := range cb.sig.Params().Variables() {
			if holdsCode(variable.Type(), map[types.Type]bool{}) {
				v.unsupported(arg.Pos(), fmt.Sprintf("%s is handed to %s as %s, which %s calls with a value of type %s, and %s may run code that it carries that nobody has seen; "+
					"hand over a function literal, or a function or method of this package that is verified", types.ExprString(arg), fn.obj.Name(), param.Name(),
					fn.obj.Name(), types.TypeString(variable.Type(), types.RelativeTo(v.pass.Pkg)), what))
			}
		}
	}
	if callee == nil {
		carriesCode("a function value from code that is not verified")
		T := v.valueContract(v.info.TypeOf(arg))
		if T == nil {
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to %s as %s, which %s calls, and its type %s has no contract; "+
				"hand over a function literal, a function, a method value, or a value of a named function type with a contract",
				types.ExprString(arg), fn.obj.Name(), param.Name(), fn.obj.Name(), v.info.TypeOf(arg)))
		}
		T = v.usable(arg.Pos(), T, T.obj.Name(), st, guard, true)
		fun := v.eval(arg, st, guard)
		v.check(st, guard, logic.Ne(fun[0], logic.RefLit(0)), arg.Pos(), "the function value %s may be nil", types.ExprString(arg))
		return &handOver{arg: arg, contract: T, value: true}
	}
	sig := callee.Type().(*types.Signature)
	if sig.TypeParams() != nil || sig.RecvTypeParams() != nil {
		v.unsupported(arg.Pos(), "generic functions cannot be handed over yet")
	}
	c := v.contractOf(callee)
	if c == nil {
		v.unsupported(arg.Pos(), fmt.Sprintf("it hands %s to %s, and %s has no contract; annotate %s with // @ annotations so that it is verified, "+
			"%s", callee.Name(), fn.obj.Name(), callee.Name(), callee.Name(), v.addEntryAdvice(callee.FullName())))
	}
	if c.trust != nil || c.imported != nil && !c.imported.Verified {
		carriesCode("a trusted function")
	}
	view := v.viewOf(c)
	v.reportUnusable(arg.Pos(), view, v.calleeName(callee))
	if view.cut {
		v.cut(st, guard)
	}
	c = view.fn
	if mayExit(c) {
		v.unsupported(arg.Pos(), fmt.Sprintf("it hands %s, which may end the process, to %s; a function handed to a trusted function may not end the process, "+
			"since the contract of what calls it assumes that each call returns", v.calleeName(callee), fn.obj.Name()))
	}
	if c.trust != nil && !view.cut {
		v.noteUse(c, arg.Pos())
	}
	h := &handOver{arg: arg, contract: c}
	if method != nil {
		sel := inner.(*ast.SelectorExpr)
		h.recv = v.receiver(&ast.CallExpr{Fun: sel, Lparen: sel.End(), Rparen: sel.End()}, sig.Recv(), st, guard)
	}
	return h
}

// runHandedCall runs, in the state of a run, a function, method value, or
// function value that was handed over: as a call the caller makes, with
// the arguments of the run.
func (v *fnVerifier) runHandedCall(h *handOver, cb *callback, given []value, head *state, by string) []value {
	call := &ast.CallExpr{Fun: h.arg, Lparen: h.arg.End(), Rparen: h.arg.End()}
	if h.contract.obj.Type().(*types.Signature).Variadic() {
		// The run's slice is passed on as it is.
		call.Ellipsis = h.arg.End()
	}
	args := map[*types.Var]value{}
	inputs := h.contract.params
	if h.recv != nil {
		args[inputs[0]] = h.recv
		inputs = inputs[1:]
	}
	for i, param := range inputs {
		args[param] = given[i]
		call.Args = append(call.Args, &ast.Ident{NamePos: h.arg.Pos(), Name: cb.params[i].Name()})
	}
	what := types.ExprString(h.arg)
	if h.value {
		what = "the function value " + what
	}
	v.sites = append(v.sites, v.site(h.arg.Pos(), "in %s run by %s at %s", what, by, v.placeOf(h.arg.Pos())))
	defer func() { v.sites = v.sites[:len(v.sites)-1] }()
	return v.invoke(call, h.contract, args, head, nil)
}

// handedSites adds to the effects of the runs of a call what a function,
// method value, or function value handed to it may write, by its contract.
// Only the receiver of a method value names an object both where it is
// handed over and in its runs.
func (v *fnVerifier) handedSites(arg ast.Expr, contract *funcInfo, eff *effects) {
	view := v.viewOf(contract)
	if view.cut {
		return
	}
	contract = view.fn
	sel, isMethod := ast.Unparen(arg).(*ast.SelectorExpr)
	var recv *types.Var
	if selection := v.info.Selections[sel]; isMethod && selection != nil && selection.Kind() == types.MethodVal && len(selection.Index()) == 1 {
		recv = contract.params[0]
	}
	for _, m := range contract.modifies {
		form, _, err := v.locateTarget(contract, m, nil, nil, nil)
		if err != nil {
			v.misread(m.clause, err)
		}
		at := site{cells: form.cells, elem: form.elem, mapType: form.mapType, lo: form.lo, hi: form.hi}
		if form.direct && recv != nil && form.param == recv {
			at.root = v.holder(sel.X, recv.Type())
		}
		eff.sites = append(eff.sites, at)
		eff.sites = append(eff.sites, v.pointerStatesSites(form, at)...)
	}
}

// handedFunc says what an argument handed to a trusted function to call
// is, as the analysis of calls through function values needs it: a
// literal, a function or the method of a method value, or, when it returns
// neither, a function value.
func (pv *pkgVerifier) handedFunc(arg ast.Expr) (*types.Func, bool) {
	switch e := ast.Unparen(arg).(type) {
	case *ast.FuncLit:
		return nil, true
	case *ast.Ident:
		named, _ := pv.info.Uses[e].(*types.Func)
		return named, false
	case *ast.SelectorExpr:
		if selection := pv.info.Selections[e]; selection != nil {
			method, _ := selection.Obj().(*types.Func)
			return method, false
		}
		named, _ := pv.info.Uses[e.Sel].(*types.Func)
		return named, false
	}
	return nil, false
}

// handedContract returns the contract of what a function, method value, or
// function value handed over runs, if it has one usable.
func (v *fnVerifier) handedContract(arg ast.Expr) *funcInfo {
	named, isLit := v.pkgVerifier.handedFunc(arg)
	var contract *funcInfo
	switch {
	case isLit:
	case named != nil:
		contract = v.contractOf(named)
	default:
		contract = v.valueContract(v.info.TypeOf(arg))
	}
	if contract == nil || contract.broken {
		return nil
	}
	return contract
}
