package vego

import (
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A verified function may take a function of a type without a name and
// call it while it runs, as each(xs, f) and filter(xs, keep) do. A Calls
// annotation in its doc comment gives such a parameter the contract the
// trust file's calls gives one of a trusted function (D2 of F40):
//
//	// @Calls f(x) When 0 <= x < 100
//
// names the parameters of f's type and says, with When, what holds at each
// call of f, read in the state of that call. The claim is the same, and
// one thing more: the function calls f only while it runs, on its own
// goroutine, with arguments that meet When; and its contract holds for
// every f that meets When, returns, and writes nothing that its Modifies
// covers, as it was when the function was called, nor any allocation that
// one of its other parameters refers to directly (the array of a slice, the
// struct a pointer points to, a map). A caller hands f over as it hands a
// function to a trusted one under calls, and every write of a run is
// checked against both. Inside the function, f is only called; each call
// checks When and forgets all memory but those two parts, the variables of
// packages included.

// readSourceCalls reads the Calls annotations of a verified function into
// contracts of its function parameters.
func (pv *pkgVerifier) readSourceCalls(fn *funcInfo) {
	if len(fn.callsClauses) == 0 {
		return
	}
	// A contract of another package is reported where it is used.
	report := func(pos token.Pos, format string, args ...any) {
		if fn.imported != nil {
			fn.defect(format, args...)
			return
		}
		pv.report(pos, format, args...)
		fn.broken = true
	}
	byName := map[string][]*clause{}
	var order []string
	for _, c := range fn.callsClauses {
		head, when, _ := strings.Cut(c.text, " When ")
		name, params, ok := parseCallsHead(strings.TrimSpace(head))
		if !ok {
			report(c.pos, "a Calls annotation names a function parameter and its parameters, as in // @Calls f(x) When 0 <= x, and %q does not", c.text)
			continue
		}
		param := fn.paramNames[name]
		switch {
		case param == nil:
			report(c.pos, "a Calls annotation names %s, which is not a parameter of %s", name, fn.obj.Name())
			continue
		case !isFunc(param.Type()) || types.Unalias(param.Type()) != param.Type().Underlying():
			why := "is not a function type"
			if isFunc(param.Type()) {
				why = "has a name; a named function type carries a contract of its own, in its doc comment"
			}
			report(c.pos, "a Calls annotation gives %s a contract, and its type %s %s", name, param.Type(), why)
			continue
		}
		sig := param.Type().(*types.Signature)
		if len(params) != sig.Params().Len() {
			report(c.pos, "a Calls annotation names %d parameters for %s, whose type %s has %d", len(params), name, param.Type(), sig.Params().Len())
			continue
		}
		key := name + "(" + strings.Join(params, ", ") + ")"
		if prior := byName[name]; len(prior) > 0 {
			priorHead, _, _ := strings.Cut(prior[0].text, " When ")
			if priorName, priorParams, _ := parseCallsHead(strings.TrimSpace(priorHead)); priorName+"("+strings.Join(priorParams, ", ")+")" != key {
				report(c.pos, "the Calls annotations of %s name the parameters of %s in two ways; name them the same in each", fn.obj.Name(), name)
				continue
			}
		}
		if byName[name] == nil {
			order = append(order, name)
		}
		byName[name] = append(byName[name], c)
		if when != "" {
			node, err := logic.ParseFormula(when)
			if err != nil {
				report(c.pos, "syntax error in the When of a Calls annotation: %v", err)
				continue
			}
			c.node = node
		}
	}
	for _, name := range order {
		clauses := byName[name]
		param := fn.paramNames[name]
		sig := param.Type().(*types.Signature)
		_, params, _ := parseCallsHead(strings.TrimSpace(strings.SplitN(clauses[0].text, " When ", 2)[0]))
		cb := &callback{param: param, sig: sig, source: true}
		// It names the constants and variables of the function's package,
		// as its contract does, also where another package reads it.
		cb.fn = &funcInfo{obj: fn.obj, decl: fn.decl, imported: fn.imported, paramNames: map[string]*types.Var{}, resultNames: map[string]int{}, vouches: map[int]bool{}}
		for n, p := range fn.paramNames {
			cb.fn.paramNames[n] = p
		}
		for i, pname := range params {
			if fn.paramNames[pname] != nil {
				report(clauses[0].pos, "a Calls annotation names a parameter of %s %s, which is a parameter of %s already; rename it", name, pname, fn.obj.Name())
				return
			}
			named := types.NewVar(clauses[0].pos, fn.obj.Pkg(), pname, sig.Params().At(i).Type())
			cb.params = append(cb.params, named)
			cb.fn.params = append(cb.fn.params, named)
			cb.fn.paramNames[pname] = named
		}
		cb.fn.params = append(cb.fn.params, fn.params...)
		for variable := range sig.Params().Variables() {
			if _, modelled := layoutOf(variable.Type()); !modelled {
				report(clauses[0].pos, "a Calls annotation gives %s a contract, and its type %s takes a %s, which is not supported", name, param.Type(), variable.Type())
				return
			}
		}
		for variable := range sig.Results().Variables() {
			if _, modelled := layoutOf(variable.Type()); !modelled {
				report(clauses[0].pos, "a Calls annotation gives %s a contract, and its type %s returns a %s, which is not supported", name, param.Type(), variable.Type())
				return
			}
		}
		for _, c := range clauses {
			if c.node == nil {
				continue
			}
			if mentionsOld(c.node) {
				report(c.pos, "the When of a Calls annotation uses old, which has no meaning there: it is read in the state at each call of %s", name)
				return
			}
			cb.requires = append(cb.requires, &clause{kind: "When", text: c.text[strings.Index(c.text, " When ")+len(" When "):], node: c.node, pos: c.pos, res: c.res})
		}
		cb.fn.requires = cb.requires
		fn.runs.set(param, true)
		fn.calls.set(param, cb)
	}
}

// parseCallsHead reads f(x, y) into its name and the names of its
// parameters.
func parseCallsHead(head string) (name string, params []string, ok bool) {
	open := strings.IndexByte(head, '(')
	if open <= 0 || !strings.HasSuffix(head, ")") {
		return "", nil, false
	}
	name = strings.TrimSpace(head[:open])
	if !token.IsIdentifier(name) {
		return "", nil, false
	}
	inner := strings.TrimSpace(head[open+1 : len(head)-1])
	if inner == "" {
		return name, nil, true
	}
	for _, p := range strings.Split(inner, ",") {
		p = strings.TrimSpace(p)
		if !token.IsIdentifier(p) || slices.Contains(params, p) || slices.Contains(logic.Reserved, p) {
			return "", nil, false
		}
		params = append(params, p)
	}
	return name, params, true
}

// sourceCallback returns the contract under Calls of the function being
// verified for a call of one of its parameters, or nil.
func (v *fnVerifier) sourceCallback(call *ast.CallExpr) *callback {
	id, ok := ast.Unparen(call.Fun).(*ast.Ident)
	if !ok {
		return nil
	}
	variable, _ := v.info.Uses[id].(*types.Var)
	if variable == nil || v.fn.calls.len() == 0 {
		return nil
	}
	cb := v.fn.calls.get(variable)
	if cb == nil || !cb.source {
		return nil
	}
	return cb
}

// exceptCalls is what a call of a parameter under Calls may not write: the
// targets of the function's Modifies on entry, and the allocations its
// other parameters refer to directly on entry, in their regions.
type exceptCalls struct {
	kept []target
}

// directTargets returns, as targets, the allocations that the parameters
// of a function other than those under calls refer to directly, in the
// values given: the whole array of a slice, up to its capacity and beyond,
// the struct a pointer points to, and a map, each in the regions of its
// type. One function computes it for the caller's check of each run and
// for what the function keeps across a call (F1 of the design review).
func (v *fnVerifier) directTargets(fn *funcInfo, args map[*types.Var]value) []target {
	var direct []target
	for _, param := range fn.params {
		val := args[param]
		if val == nil || fn.calls.get(param) != nil {
			continue
		}
		t := param.Type()
		switch {
		case isSlice(t):
			if cells := v.cellsOf(elemType(t)); len(cells) > 0 {
				direct = append(direct, target{cells: cells, elem: elemType(t), ref: val[0]})
			}
		case isMap(t):
			direct = append(direct, target{mapType: t, ref: val[0]})
		default:
			if object, isPointer := pointee(t); isPointer && isStructType(object) {
				if cells := v.cellsOf(object); len(cells) > 0 {
					direct = append(direct, target{cells: cells, ref: val[0]})
				}
			}
		}
	}
	return direct
}

// keptBy states that a cell is one a call of a parameter under Calls does
// not write: in what the function's Modifies covers, or in an allocation
// one of its other parameters refers to directly.
func (v *fnVerifier) keptBy(e *exceptCalls, key string, ref, position *logic.Term) *logic.Term {
	var kept []*logic.Term
	for _, t := range e.kept {
		kept = append(kept, logic.Not(v.untouchedBy(t, key, ref, position)))
	}
	return logic.Or(kept...)
}

// callSourceParam verifies a call of a parameter under Calls in the body
// of the function that has it: the arguments are evaluated, When is
// proved, and every cell but what the function may write and what its
// other parameters refer to directly is forgotten.
func (v *fnVerifier) callSourceParam(call *ast.CallExpr, cb *callback, st *state, guard []*logic.Term) []value {
	u := v.unit
	operands := u.pushCeiling()
	given := make([]value, len(cb.params))
	for i, passed := range v.bindCall(call, cb.sig) {
		given[i] = v.evalPassed(passed, st, guard)
	}
	u.reach(operands)
	name := types.ExprString(call.Fun)
	for _, fact := range v.callRequires(cb, given, v.entry, st) {
		text := ""
		for _, c := range cb.requires {
			text = c.text
		}
		v.check(st, guard, fact, call.Pos(), "the When of the Calls annotation of %s may not hold at this call: %s", name, text)
	}
	except := v.callsExcept()
	// A call inside a run of what another function was handed may write
	// only what that function lets a run write: what it may write itself
	// must lie in what this call keeps (F2 of the design review).
	for _, f := range v.forbidden {
		what := "what " + f.by + " may write itself while it runs the function it was handed"
		if f.direct {
			what = "what an argument of " + f.by + " refers to directly, which a function it calls under Calls may not write"
		}
		for _, t := range f.targets {
			v.check(st, guard, v.coveredBy(except, t), call.Pos(),
				"%s may write %s, since %s may write anything but what %s may write and what its other parameters refer to directly",
				name, what, name, v.fn.obj.Name())
		}
	}
	// A map a loop ranges over may get keys from the call unless the
	// call keeps it (F5).
	for _, r := range v.ranges {
		v.check(st, guard, v.keptBy(except, mapOwner(r.walk.mapType)+hasLeaf.path, r.walk.ref, logic.IntLit(0)), call.Pos(),
			"%s may modify %s while the loop at %s ranges over it, and may add a key, which Go may or may not visit during the loop, "+
				"since %s may write anything but what %s may write and what its other parameters refer to directly; call it after the loop",
			name, r.text, v.placeOf(r.at), name, v.fn.obj.Name())
	}
	v.startCallsEpoch(st, except, guard)
	existed := st.brk
	st.brk = v.fresh("brk", logic.Ref)
	st.assume(logic.Le(existed, st.brk))
	if len(guard) > 0 {
		st.assume(logic.Implies(logic.Not(logic.And(guard...)), logic.Eq(st.brk, existed)))
	}
	mark, known := len(v.made), len(st.hyps)
	results := make([]value, cb.sig.Results().Len())
	for i := range results {
		results[i] = v.unknown(name, cb.sig.Results().At(i).Type(), st)
	}
	// Nothing but its types says what the call returns, so a function
	// whose success hangs on it cannot promise success (F13 of the design
	// review of F40): the call is a source of unpredictable failure.
	handed := forward{produced: slices.Clip(v.made[mark:]), facts: slices.Clip(st.hyps[known:])}
	for _, taken := range st.chosen {
		handed.path = append(handed.path, taken.cond)
	}
	for _, val := range given {
		handed.given = append(handed.given, val...)
	}
	v.forwards = append(v.forwards, handed)
	if v.tracksFailure && len(results) > 0 && v.canReach(st.hyps) {
		source := failureSource{outputs: map[string]bool{}, origins: []forward{handed}}
		for _, produced := range handed.produced {
			source.outputs[produced] = true
		}
		v.sources = append(v.sources, source)
	}
	u.calls = append(u.calls, unitCall{name: name, pos: call.Pos()})
	u.wrote(st, "the call to "+name)
	u.event()
	return results
}

// callsExcept returns what a call of a parameter under Calls of the
// function being verified keeps.
func (v *fnVerifier) callsExcept() *exceptCalls {
	return &exceptCalls{kept: slices.Concat(v.frame, v.directTargets(v.fn, v.entry))}
}

// coveredBy states that every cell of a target is one a call of a
// parameter under Calls keeps.
func (v *fnVerifier) coveredBy(e *exceptCalls, t target) *logic.Term {
	var cells []*logic.Term
	t.regions(func(key string, _ logic.Sort) {
		k := v.bound("k")
		inside := logic.Not(v.untouchedBy(t, key, t.ref, k))
		cells = append(cells, logic.Forall(k, logic.Implies(inside, v.keptBy(e, key, t.ref, k))))
	})
	return logic.Or(logic.Eq(t.ref, logic.RefLit(0)), logic.And(cells...))
}

// untouchedBy states that a cell of a region is not one a target covers,
// as the layers of havoc and of loops read a target. A target of a form it
// does not tell apart cell by cell counts as covering nothing, which only
// keeps less.
func (v *fnVerifier) untouchedBy(t target, key string, ref, index *logic.Term) *logic.Term {
	switch {
	case t.except != nil:
		return logic.True()
	case !t.fp && !t.reaches([]string{key}):
		return logic.True()
	case t.fp:
		position := index
		if isMapRegion(key) {
			position = logic.IntLit(0)
		}
		outside, _ := v.outsideFootprint(t, key, ref, position)
		return outside
	case t.row && !inRowRegions(t.cells, key):
		return logic.True()
	case t.key != nil:
		return logic.True()
	case t.lo == nil:
		return logic.Ne(ref, t.ref)
	case t.single:
		var untouched []*logic.Term
		for _, c := range t.cells {
			if c.key != key {
				continue
			}
			lo, hi := c.start(t.lo), c.end(t.lo)
			if !c.isRun() {
				hi = logic.Add(lo, logic.IntLit(1))
			}
			untouched = append(untouched, logic.Not(logic.And(logic.Eq(ref, t.ref), logic.Le(lo, index), logic.Lt(index, hi))))
		}
		return logic.And(untouched...)
	case strings.HasSuffix(key, countLeaf.path):
		return logic.Ne(ref, t.ref)
	}
	return logic.Not(logic.And(logic.Eq(ref, t.ref), logic.Le(t.lo, index), logic.Lt(index, t.hi)))
}

// startCallsEpoch makes every region of memory, also one not yet in the
// map and those of the variables of packages, a new unknown that keeps
// only what a call of a parameter under Calls does not write.
func (v *fnVerifier) startCallsEpoch(st *state, except *exceptCalls, guard []*logic.Term) {
	t := target{fp: true, except: except}
	if len(guard) > 0 {
		t.skipped = logic.Not(logic.And(guard...))
	}
	e := v.fresh(allEpoch, logic.Int)
	v.epochs[e.Name] = &epoch{before: st.mem, bound: st.brk, targets: []target{t}, by: "a call of a function parameter under Calls"}
	mem := memory{epochKey: e}
	if rows, ok := st.mem[footprintRegion]; ok {
		mem[footprintRegion] = rows
	}
	st.mem = mem
}

// allEpoch begins the name of an epoch that also covers the variables of
// packages, which a call of a parameter under Calls may write.
const allEpoch = "epochall"

// checkSourceCallsUses refuses every use of a parameter under Calls but a
// call of it: one that is stored, returned, compared, or handed on would
// outlive the claim, which holds only while the function calls it.
func (v *fnVerifier) checkSourceCallsUses() {
	if v.fn.calls.len() == 0 || v.fn.decl == nil || v.fn.decl.Body == nil {
		return
	}
	var stack []ast.Node
	ast.Inspect(v.fn.decl.Body, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		stack = append(stack, n)
		id, ok := n.(*ast.Ident)
		if !ok {
			return true
		}
		variable, _ := v.info.Uses[id].(*types.Var)
		if variable == nil {
			return true
		}
		cb := v.fn.calls.get(variable)
		if cb == nil || !cb.source {
			return true
		}
		var parent ast.Node
		for i := len(stack) - 2; i >= 0; i-- {
			if _, paren := stack[i].(*ast.ParenExpr); !paren {
				parent = stack[i]
				break
			}
		}
		if call, isCall := parent.(*ast.CallExpr); isCall && ast.Unparen(call.Fun) == id {
			return true
		}
		v.unsupported(id.Pos(), "the Calls annotation of "+v.fn.obj.Name()+" gives "+id.Name+" a contract that holds only while "+v.fn.obj.Name()+
			" calls it, and here it is used other than by calling it: stored, returned, compared, or handed on; a function that travels needs a named function type with a contract")
		return true
	})
}

// sourceCallsOf returns the contract of a verified function whose Calls
// annotations give its function parameters contracts, or nil.
func (pv *pkgVerifier) sourceCallsOf(callee *types.Func) *funcInfo {
	if own := pv.funcs[callee]; own != nil && own.calls.len() > 0 && own.trust == nil {
		return own
	}
	if imported := pv.importedContract(callee); imported != nil && imported.calls.len() > 0 {
		return imported
	}
	return nil
}
