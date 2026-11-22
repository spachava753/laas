package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"

	"golang.org/x/tools/go/cfg"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A verified function that lists a footprint parameter assumes that its
// footprint holds no cell that the other parameters reach without going
// through an interface value (see enterReaches). A verified caller proves
// that at each call from where its arguments came, without asking Z3:
// every value the function holds is either outside or unknown, and the
// function is either clean or polluted.
//
// The invariants the rules keep (recorded in the ROADMAP, Footprints):
//
//   - A value is outside at a point when everything reachable from it
//     without passing through an interface value lies outside the row of
//     every footprint parameter the function lists, at that point.
//   - A function is clean at a point when no reference of unknown origin
//     has been stored into memory that an outside value reaches.
//
// A parameter that is not an interface value is outside on entry, by the
// function's own assumption, and so is memory the function creates. A
// value read through an outside value is outside while the function is
// clean. A callee may return or store memory it got other than
// through its arguments, from its package or from a call it made (F28 of
// the review of step 2), so the result of a call is outside only when it
// holds no memory, when the contract says it is new and the call writes no
// footprint, or when the contract places it within an argument that is
// outside. Everything else is unknown. A store of an unknown reference into
// memory, or a call whose targets can hold a reference, whatever it is
// handed, pollutes the function. A variable that a function literal
// assigns is judged by what holds anywhere (F29). Rows grow only by
// memory created at calls through their value, which no outside value
// reaches, so outside stays outside along the path.
//
// The analysis runs over the control-flow graph of the declared function,
// as the origins of errors do, so a store late in a loop's body reaches a
// call early in the next iteration, and at a join the worse wins. A call
// inside a function literal, and a deferred call, which runs at a return,
// are judged by what holds anywhere in the function.

// memFact is what holds at one point: the variables that hold an unknown
// value, each with why, and why the function is polluted, or "".
type memFact struct {
	unknown  map[*types.Var]string
	polluted string
}

func (f memFact) clone() memFact {
	return memFact{unknown: maps.Clone(f.unknown), polluted: f.polluted}
}

// join adds what another fact says, and reports whether that changed f.
func (f *memFact) join(g memFact) bool {
	changed := false
	for variable, why := range g.unknown {
		if _, known := f.unknown[variable]; !known {
			f.unknown[variable] = why
			changed = true
		}
	}
	if f.polluted == "" && g.polluted != "" {
		f.polluted = g.polluted
		changed = true
	}
	return changed
}

// memFlow is the analysis of one body: the fact before each call, and the
// fact that holds anywhere in the body, literals included.
type memFlow struct {
	at    map[*ast.CallExpr]memFact
	loose memFact
	// litAssigned holds the variables declared outside a function literal
	// that the literal assigns.
	litAssigned map[*types.Var]bool
}

// memOrigins returns the analysis of the declared function being verified.
func (v *fnVerifier) memOrigins() *memFlow {
	if v.memFlowDone != nil {
		return v.memFlowDone
	}
	flow := &memFlow{at: map[*ast.CallExpr]memFact{}, loose: memFact{unknown: map[*types.Var]string{}}, litAssigned: map[*types.Var]bool{}}
	v.memFlowDone = flow
	body := v.bodyOrigin()
	if body == nil {
		return flow
	}
	ast.Inspect(body, func(n ast.Node) bool {
		lit, ok := n.(*ast.FuncLit)
		if !ok {
			return true
		}
		ast.Inspect(lit.Body, func(m ast.Node) bool {
			var targets []ast.Expr
			switch m := m.(type) {
			case *ast.AssignStmt:
				targets = m.Lhs
			case *ast.IncDecStmt:
				targets = []ast.Expr{m.X}
			case *ast.RangeStmt:
				targets = []ast.Expr{m.Key, m.Value}
			}
			for _, target := range targets {
				if id, ok := ast.Unparen(target).(*ast.Ident); ok && target != nil {
					if variable, isVar := v.info.ObjectOf(id).(*types.Var); isVar && (variable.Pos() < lit.Pos() || variable.Pos() >= lit.End()) {
						flow.litAssigned[variable] = true
					}
				}
			}
			return true
		})
		return true
	})
	// What holds anywhere: the least fixed point over every node of the
	// body and of its literals.
	for changed := true; changed; {
		changed = false
		ast.Inspect(body, func(n ast.Node) bool {
			switch n.(type) {
			case ast.Stmt, ast.Expr:
				next := flow.loose.clone()
				v.memTransfer(n, &next, flow.loose, false)
				if flow.loose.join(next) {
					changed = true
				}
			}
			return true
		})
	}
	graph := cfg.New(body, func(*ast.CallExpr) bool { return true })
	in := map[*cfg.Block]*memFact{}
	for _, block := range graph.Blocks {
		in[block] = &memFact{unknown: map[*types.Var]string{}}
	}
	work := slices.Clone(graph.Blocks)
	for len(work) > 0 {
		block := work[len(work)-1]
		work = work[:len(work)-1]
		out := in[block].clone()
		for _, node := range block.Nodes {
			v.memTransfer(node, &out, flow.loose, true)
		}
		for _, succ := range block.Succs {
			if in[succ].join(out) && !slices.Contains(work, succ) {
				work = append(work, succ)
			}
		}
	}
	// The fact before each call: before its node, with every pollution of
	// the node itself, which may come before the call.
	for _, block := range graph.Blocks {
		fact := in[block].clone()
		for _, node := range block.Nodes {
			own := fact.clone()
			v.memTransfer(node, &own, flow.loose, true)
			before := fact.clone()
			before.polluted = firstReason(before.polluted, own.polluted)
			ast.Inspect(node, func(n ast.Node) bool {
				if _, isLit := n.(*ast.FuncLit); isLit {
					return false
				}
				if call, ok := n.(*ast.CallExpr); ok {
					flow.at[call] = before
				}
				return true
			})
			fact = own
		}
	}
	return flow
}

// firstReason returns the first of two reasons that is not empty.
func firstReason(a, b string) string {
	if a != "" {
		return a
	}
	return b
}

// memTransfer applies what one node does: the variables it assigns and
// what its stores and calls pollute. local is set when the node is one of
// the control-flow graph, whose variables are judged along the path;
// otherwise they are judged by loose, what holds anywhere.
func (v *fnVerifier) memTransfer(n ast.Node, fact *memFact, loose memFact, local bool) {
	judge := *fact
	if !local {
		judge = loose
	}
	// Calls, appends, and literals that run in place or are handed over.
	ast.Inspect(n, func(m ast.Node) bool {
		switch m := m.(type) {
		case *ast.FuncLit:
			// A literal's body is judged where it is: walked by the
			// fixed point over every node, and by the call that runs it.
			return false
		case *ast.CallExpr:
			if why := v.callPollutes(m, judge); why != "" && fact.polluted == "" {
				fact.polluted = why
			}
		}
		return true
	})
	assign := func(lhs ast.Expr, why string, rhsType types.Type) {
		lhs = ast.Unparen(lhs)
		if id, ok := lhs.(*ast.Ident); ok {
			variable, isVar := v.info.ObjectOf(id).(*types.Var)
			if !isVar || id.Name == "_" {
				return
			}
			if v.boxed[variable] || variable.Parent() == v.pass.Pkg.Scope() {
				if why != "" && fact.polluted == "" {
					fact.polluted = fmt.Sprintf("at %s a value was stored into %s, which lives in memory, and %s", v.placeOf(id.Pos()), id.Name, why)
				}
			}
			if why != "" {
				fact.unknown[variable] = why
			} else if local {
				delete(fact.unknown, variable)
			}
			return
		}
		if root, inMemory := v.storePlace(lhs); !inMemory && root != nil {
			// A part of a local struct value.
			if why != "" {
				fact.unknown[root] = why
			}
			return
		}
		if why != "" && rhsType != nil && holdsMemory(rhsType) && fact.polluted == "" {
			fact.polluted = fmt.Sprintf("at %s a value was stored into memory, and %s", v.placeOf(lhs.Pos()), why)
		}
	}
	switch n := n.(type) {
	case *ast.AssignStmt:
		if len(n.Lhs) == len(n.Rhs) {
			for i, lhs := range n.Lhs {
				assign(lhs, v.memOrigin(n.Rhs[i], judge), v.info.TypeOf(n.Rhs[i]))
			}
		} else if len(n.Rhs) == 1 {
			for i, lhs := range n.Lhs {
				assign(lhs, v.memResult(n.Rhs[0], i, judge), v.info.TypeOf(lhs))
			}
		}
	case *ast.ValueSpec:
		for i, name := range n.Names {
			switch {
			case len(n.Values) == len(n.Names):
				assign(name, v.memOrigin(n.Values[i], judge), v.info.TypeOf(n.Values[i]))
			case len(n.Values) == 1:
				assign(name, v.memResult(n.Values[0], i, judge), v.info.TypeOf(name))
			}
		}
	case *ast.DeclStmt:
		if decl, ok := n.Decl.(*ast.GenDecl); ok {
			for _, spec := range decl.Specs {
				if value, ok := spec.(*ast.ValueSpec); ok {
					v.memTransfer(value, fact, loose, local)
				}
			}
		}
	case *ast.RangeStmt:
		// Outside the graph only: there the key and the value are what the
		// ranged value holds.
		why := v.memOrigin(n.X, judge)
		for _, e := range []ast.Expr{n.Key, n.Value} {
			if e != nil {
				assign(e, why, v.info.TypeOf(e))
			}
		}
	}
	if !local {
		return
	}
	// go/cfg puts the key and the value of a range once before the loop,
	// at the range expression; they hold what the ranged value holds, or
	// anything the variable it is read from is ever given.
	if expr, ok := n.(ast.Expr); ok {
		if rs := v.rangeOf(expr); rs != nil {
			why := firstReason(v.memOrigin(rs.X, judge), v.memOrigin(rs.X, loose))
			for _, e := range []ast.Expr{rs.Key, rs.Value} {
				if e != nil {
					assign(e, why, v.info.TypeOf(e))
				}
			}
		}
	}
}

// rangeOf returns the range statement whose ranged expression is e.
func (v *fnVerifier) rangeOf(e ast.Expr) *ast.RangeStmt {
	if v.ranged == nil {
		v.ranged = map[ast.Expr]*ast.RangeStmt{}
		if body := v.bodyOrigin(); body != nil {
			ast.Inspect(body, func(n ast.Node) bool {
				if rs, ok := n.(*ast.RangeStmt); ok {
					v.ranged[rs.X] = rs
				}
				return true
			})
		}
	}
	return v.ranged[e]
}

// storePlace returns the local variable a target of an assignment is part
// of, and whether the target lies in memory: through a pointer, a slice, a
// map, or a variable whose address is taken.
func (v *fnVerifier) storePlace(e ast.Expr) (*types.Var, bool) {
	for {
		switch x := ast.Unparen(e).(type) {
		case *ast.Ident:
			variable, _ := v.info.ObjectOf(x).(*types.Var)
			return variable, variable == nil || v.boxed[variable] || variable.Parent() == v.pass.Pkg.Scope()
		case *ast.SelectorExpr:
			if _, isPointer := pointee(v.info.TypeOf(x.X)); isPointer {
				return nil, true
			}
			e = x.X
		case *ast.IndexExpr:
			if t := v.info.TypeOf(x.X); isSlice(t) || isMap(t) {
				return nil, true
			}
			e = x.X
		default:
			return nil, true
		}
	}
}

// memOrigin returns why a value may be unknown, or "" when it is outside.
func (v *fnVerifier) memOrigin(e ast.Expr, fact memFact) string {
	t := v.info.TypeOf(e)
	if t == nil || !holdsMemory(t) {
		return ""
	}
	switch x := ast.Unparen(e).(type) {
	case *ast.Ident:
		variable, isVar := v.info.ObjectOf(x).(*types.Var)
		if !isVar {
			return ""
		}
		// A literal may assign the variable at any call that runs it, in
		// place or handed over, which the path does not see (F29 of the
		// review of step 2).
		if flow := v.memOrigins(); flow.litAssigned[variable] {
			return firstReason(fact.unknown[variable], flow.loose.unknown[variable])
		}
		return fact.unknown[variable]
	case *ast.SelectorExpr:
		if selection := v.info.Selections[x]; selection != nil && selection.Kind() != types.FieldVal {
			return "it is a method value"
		}
		if selection := v.info.Selections[x]; selection == nil {
			// A package-level variable of another package.
			return ""
		}
		return v.memOrigin(x.X, fact)
	case *ast.IndexExpr:
		return v.memOrigin(x.X, fact)
	case *ast.SliceExpr:
		return v.memOrigin(x.X, fact)
	case *ast.StarExpr:
		return v.memOrigin(x.X, fact)
	case *ast.UnaryExpr:
		if x.Op == token.AND {
			return v.memOrigin(x.X, fact)
		}
		return ""
	case *ast.CompositeLit:
		for _, elt := range x.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				elt = kv.Value
			}
			if why := v.memOrigin(elt, fact); why != "" {
				return why
			}
		}
		return ""
	case *ast.CallExpr:
		return v.memResult(x, 0, fact)
	}
	return fmt.Sprintf("its origin at %s is not known", v.placeOf(e.Pos()))
}

// memResult returns why a result of a call may be unknown, or "".
func (v *fnVerifier) memResult(e ast.Expr, index int, fact memFact) string {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok {
		if index == 0 {
			return v.memOrigin(e, fact)
		}
		// A map read or a receive with its second result.
		return ""
	}
	if tv, ok := v.info.Types[call.Fun]; ok && tv.IsType() {
		// A conversion.
		if len(call.Args) == 1 {
			return v.memOrigin(call.Args[0], fact)
		}
		return ""
	}
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		if builtin, isBuiltin := v.info.Uses[id].(*types.Builtin); isBuiltin {
			switch builtin.Name() {
			case "append":
				for _, arg := range call.Args {
					if why := v.memOrigin(arg, fact); why != "" {
						return why
					}
				}
			}
			return ""
		}
	}
	name := types.ExprString(call.Fun)
	if t := v.resultType(call, index); t != nil && !holdsMemory(t) {
		return ""
	}
	fn := v.memCallee(call)
	if fn == nil {
		return fmt.Sprintf("it comes from the call of %s at %s, which has no contract", name, v.placeOf(call.Pos()))
	}
	// A callee may return memory it got other than through its arguments,
	// from its package or from a call it made (F28 of the review of step
	// 2), so only a contract can place what it returns: new, or within an
	// argument that is outside.
	if promisesFresh(fn, index) && !writesFootprint(v, fn) {
		return ""
	}
	if arg := v.withinArg(call, fn, index); arg != nil {
		if why := v.memOrigin(arg, fact); why != "" {
			return fmt.Sprintf("it comes from the call of %s at %s, whose contract places it within %s, and %s", name, v.placeOf(call.Pos()), types.ExprString(arg), why)
		}
		return ""
	}
	return fmt.Sprintf("it comes from the call of %s at %s, whose contract does not say that it is new or lies within an argument", name, v.placeOf(call.Pos()))
}

// resultType returns the type of a result of a call, or nil.
func (v *fnVerifier) resultType(call *ast.CallExpr, index int) types.Type {
	switch t := v.info.TypeOf(call).(type) {
	case *types.Tuple:
		if index < t.Len() {
			return t.At(index).Type()
		}
		return nil
	default:
		if index == 0 {
			return t
		}
		return nil
	}
}

// withinArg returns the argument that a top-level conjunct of the callee's
// Ensures places a result within, as within(r, p) or fresh(r) Or
// within(r, p), or nil.
func (v *fnVerifier) withinArg(call *ast.CallExpr, fn *funcInfo, index int) ast.Expr {
	if index >= len(fn.results) {
		return nil
	}
	name := spelledResult(fn, index)
	isResult := func(n *logic.Node) bool { return n.Kind == logic.NIdent && n.Name == name && !n.Primed }
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			if conjunct.Kind == logic.NBinary && conjunct.Op == "Or" {
				a, b := conjunct.Kids[0], conjunct.Kids[1]
				if b.Kind == logic.NCall && b.Name == "fresh" {
					a, b = b, a
				}
				if a.Kind == logic.NCall && a.Name == "fresh" && len(a.Kids) == 1 && isResult(a.Kids[0]) {
					conjunct = b
				}
			}
			if conjunct.Kind != logic.NCall || conjunct.Name != "within" || len(conjunct.Kids) != 2 ||
				!isResult(conjunct.Kids[0]) || conjunct.Kids[1].Kind != logic.NIdent || conjunct.Kids[1].Primed {
				continue
			}
			param := fn.paramNames[conjunct.Kids[1].Name]
			if param == nil {
				continue
			}
			if arg := v.argumentFor(call, fn, param); arg != nil {
				return arg
			}
		}
	}
	return nil
}

// argumentFor returns the expression a call passes for a parameter of its
// callee, the receiver included, or nil.
func (v *fnVerifier) argumentFor(call *ast.CallExpr, fn *funcInfo, param *types.Var) ast.Expr {
	sig, _ := fn.obj.Type().(*types.Signature)
	if sig == nil {
		return nil
	}
	if (sig.Recv() != nil && param == sig.Recv()) || (len(fn.params) > 0 && param == fn.params[0] && sig.Recv() != nil) {
		if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok {
			return sel.X
		}
		return nil
	}
	bound, ok := bindArgs(v.info, call, paramsOf(sig), sig.Variadic())
	if !ok {
		return nil
	}
	for _, b := range bound {
		if b.param == param && !b.packed && !b.spread {
			return b.expr
		}
	}
	return nil
}

// memCallee returns the contract a call is checked against, or nil.
func (v *fnVerifier) memCallee(call *ast.CallExpr) *funcInfo {
	if v.literalOf(call) != nil {
		return nil
	}
	method, value := throughValue(v.info, call)
	switch {
	case value:
		return v.valueContract(v.info.TypeOf(call.Fun))
	case method != nil:
		return v.methodContract(method)
	}
	callee := v.pkgVerifier.calleeAt(call)
	if callee == nil {
		return nil
	}
	return v.contractOf(callee)
}

// reachesCode reports whether a value of a type is, or reaches through
// fields, elements, and pointers, an interface value or a function value.
func reachesCode(t types.Type, seen map[types.Type]bool) bool {
	if seen[t] {
		return false
	}
	seen[t] = true
	if object, isPointer := pointee(t); isPointer {
		return reachesCode(object, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Interface, *types.Signature, *types.Chan:
		return true
	case *types.Slice:
		return reachesCode(u.Elem(), seen)
	case *types.Map:
		return reachesCode(u.Key(), seen) || reachesCode(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if reachesCode(field.Type(), seen) {
				return true
			}
		}
	case *types.Basic:
		return u.Kind() == types.UnsafePointer
	}
	return false
}

// callPollutes returns why a call may store an unknown reference into
// memory that an outside value reaches, or "".
func (v *fnVerifier) callPollutes(call *ast.CallExpr, fact memFact) string {
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		if builtin, isBuiltin := v.info.Uses[id].(*types.Builtin); isBuiltin {
			if builtin.Name() == "append" && len(call.Args) > 0 {
				// An append in place stores into the array of its slice.
				for _, arg := range call.Args[1:] {
					if why := v.memOrigin(arg, fact); why != "" {
						return fmt.Sprintf("at %s a value was appended to a slice, and %s", v.placeOf(call.Pos()), why)
					}
				}
			}
			return ""
		}
	}
	if tv, ok := v.info.Types[call.Fun]; ok && tv.IsType() {
		return ""
	}
	// A literal called in place or handed over runs its stores during the
	// call; they are judged where the literal is.
	for _, lit := range v.literalsRun(call) {
		if why := v.literalPollutes(lit); why != "" {
			return why
		}
	}
	fn := v.memCallee(call)
	if fn == nil || !v.targetsHoldReferences(fn) {
		return ""
	}
	// A callee may store memory it got other than through its arguments,
	// from its package or from a call it made, into what it modifies (F28
	// of the review of step 2), so a call whose targets can hold a
	// reference pollutes whatever it is handed.
	return fmt.Sprintf("the call of %s at %s may store into memory it may modify a reference to memory of any origin",
		types.ExprString(call.Fun), v.placeOf(call.Pos()))
}

// literalsRun returns the function literals a call runs: the one called in
// place, and those written as its arguments.
func (v *fnVerifier) literalsRun(call *ast.CallExpr) []*ast.FuncLit {
	var lits []*ast.FuncLit
	if lit := v.literalOf(call); lit != nil {
		lits = append(lits, lit)
	}
	for _, arg := range call.Args {
		if lit, ok := ast.Unparen(arg).(*ast.FuncLit); ok {
			lits = append(lits, lit)
		}
	}
	return lits
}

// literalPollutes returns why a literal's body may store an unknown
// reference into memory, judged by what holds anywhere in the function.
func (v *fnVerifier) literalPollutes(lit *ast.FuncLit) string {
	loose := v.memOrigins().loose
	why := ""
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		if why != "" {
			return false
		}
		switch n.(type) {
		case ast.Stmt, ast.Expr:
			probe := memFact{unknown: maps.Clone(loose.unknown)}
			v.memTransfer(n, &probe, loose, false)
			why = probe.polluted
		}
		return true
	})
	return why
}

// targetsHoldReferences reports whether something a contract may modify,
// other than the footprint or the states of an interface value, can hold a
// reference.
func (v *fnVerifier) targetsHoldReferences(fn *funcInfo) bool {
	view := v.viewOf(fn)
	if view.cut {
		return false
	}
	for _, m := range view.fn.modifies {
		form, _, err := v.locateTarget(view.fn, m, nil, nil, nil)
		if err != nil {
			return true
		}
		switch {
		case form.fp || form.row:
		case form.mapType != nil:
			if _, elem := mapParts(form.mapType); holdsMemory(elem) || isIface(elem) {
				return true
			}
		default:
			if slices.ContainsFunc(form.cells, func(c cell) bool { return c.sort == logic.Ref }) {
				return true
			}
		}
	}
	return false
}

// writesFootprint reports whether a contract may modify the footprint of
// an interface value.
func writesFootprint(v *fnVerifier, fn *funcInfo) bool {
	view := v.viewOf(fn)
	if view.cut {
		return true
	}
	for _, m := range view.fn.modifies {
		if form, _, err := v.locateTarget(view.fn, m, nil, nil, nil); err != nil || form.fp {
			return true
		}
	}
	return false
}

// promisesFresh reports whether a top-level conjunct of an Ensures of a
// contract says that a result is new.
func promisesFresh(fn *funcInfo, result int) bool {
	if result >= len(fn.results) {
		return false
	}
	name := spelledResult(fn, result)
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			if conjunct.Kind == logic.NCall && conjunct.Name == "fresh" && len(conjunct.Kids) == 1 &&
				conjunct.Kids[0].Kind == logic.NIdent && conjunct.Kids[0].Name == name && !conjunct.Kids[0].Primed {
				return true
			}
		}
	}
	return false
}

// checkReachedApart proves at a call of a verified function that what each
// other argument reaches lies outside the footprint of each footprint
// argument whose parameter the callee lists, as the callee assumes. The
// footprint argument must be a parameter of the caller whose footprint the
// caller's own Modifies lists, which the caller assumes the same of; the
// other argument must be outside, and the caller clean.
func (v *fnVerifier) checkReachedApart(call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value, written []target,
	passed map[*types.Var]string, passedExpr map[*types.Var]ast.Expr, name string) {
	if fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		return
	}
	for _, t := range written {
		if !t.fp || t.param == nil {
			continue
		}
		for _, other := range fn.params {
			if other == t.param || args[other] == nil || !holdsMemory(other.Type()) {
				continue
			}
			lead := fmt.Sprintf("the footprint of what is passed to %s as %s may hold memory that what is passed as %s reaches, and %s relies on it not doing so",
				name, passed[t.param], passed[other], name)
			fact, placed := v.memFactAt(call)
			if !placed {
				v.unsupported(call.Pos(), lead+"; a caller of a function value or a method of an interface value does not show it")
			}
			if !v.ownFootprint(passedExpr[t.param]) {
				v.report(call.Pos(), "%s: %s is not a parameter whose footprint %s's own Modifies lists, so nothing places it", lead, passed[t.param], v.fn.obj.Name())
				continue
			}
			if expr := passedExpr[other]; expr == nil {
				v.report(call.Pos(), "%s: what is passed as %s is not written as one expression", lead, passed[other])
			} else if why := v.memOrigin(expr, fact); why != "" {
				v.report(call.Pos(), "%s: %s", lead, why)
			} else if fact.polluted != "" {
				v.report(call.Pos(), "%s: %s", lead, fact.polluted)
			}
		}
	}
}

// memFactAt returns what holds at a call: before it along the path, or for
// a call inside a literal or a deferred call, what holds anywhere. It
// reports false for a call that is not in the body, as the one made up to
// check a value.
func (v *fnVerifier) memFactAt(call *ast.CallExpr) (memFact, bool) {
	flow := v.memOrigins()
	fact, placed := flow.at[call]
	if !placed {
		inside := false
		if body := v.bodyOrigin(); body != nil && body.Pos() <= call.Pos() && call.End() <= body.End() {
			inside = true
		}
		return flow.loose, inside
	}
	if v.lit != nil || v.deferredCall(call) {
		return flow.loose, true
	}
	return fact, true
}

// deferredCall reports whether a call is the call of a defer statement.
func (v *fnVerifier) deferredCall(call *ast.CallExpr) bool {
	found := false
	if body := v.bodyOrigin(); body != nil {
		ast.Inspect(body, func(n ast.Node) bool {
			if d, ok := n.(*ast.DeferStmt); ok && d.Call == call {
				found = true
			}
			return !found
		})
	}
	return found
}

// ownFootprint reports whether an argument is a parameter of the function
// that its Modifies lists as a footprint, whose separation the function
// assumes on entry, and that it never assigns.
func (v *fnVerifier) ownFootprint(e ast.Expr) bool {
	if e == nil {
		return false
	}
	id, ok := ast.Unparen(e).(*ast.Ident)
	if !ok {
		return false
	}
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	if variable == nil || v.findReassigned(v.bodyOrigin())[variable] {
		return false
	}
	return slices.ContainsFunc(v.reaches, func(r separation) bool { return r.param == variable })
}
