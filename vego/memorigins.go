package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"

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
	// the node itself, which may come before the call, but that of the
	// call: what the call stores happens while it runs, which its callee
	// accounts for.
	for _, block := range graph.Blocks {
		fact := in[block].clone()
		for _, node := range block.Nodes {
			own := fact.clone()
			v.memTransfer(node, &own, flow.loose, true)
			ast.Inspect(node, func(n ast.Node) bool {
				if _, isLit := n.(*ast.FuncLit); isLit {
					return false
				}
				if call, ok := n.(*ast.CallExpr); ok {
					others := fact.clone()
					v.skipPollution = call
					v.memTransfer(node, &others, flow.loose, true)
					v.skipPollution = nil
					before := fact.clone()
					before.polluted = firstReason(before.polluted, others.polluted)
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
// packageOrigin is the origin of a package-level variable read as a
// value that refers to memory. What it refers to is outside only while
// the variable holds the only reference to it: its initialiser made that
// memory and no use in the build lets a reference to it out, which the
// proof then relies on, so that a package built later that lets one out is
// reported. Code that is not verified and holds such a reference could
// hand it in as the writer of a footprint (F1 of the design review of
// package-level variables).
func (v *fnVerifier) packageOrigin(variable *types.Var) string {
	key := errorKey(variable)
	if _, written := v.writtenInBuild()[key]; written || isError(variable.Type()) || !v.readOnlyHere(variable) {
		return fmt.Sprintf("it is read from the package-level variable %s, whose memory code elsewhere may refer to", v.spelling(variable))
	}
	for _, relied := range []string{key, key + contentsKey} {
		v.reliedKeys[relied] = true
		v.reliedValues[relied] = true
	}
	return ""
}

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
		if variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope() {
			return v.packageOrigin(variable)
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
			if variable, isVar := v.info.ObjectOf(x.Sel).(*types.Var); isVar {
				return v.packageOrigin(variable)
			}
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
	if v.pkgVerifier.memSummary(fn.obj).results && fn.trust == nil && fn.valueOf == nil && fn.methodOf == nil {
		// A verified callee returns what its arguments reach or new
		// memory, so the result is outside when they are.
		if why := v.unknownArgument(call, fact); why != "" {
			return fmt.Sprintf("it comes from the call of %s at %s, which returns what its arguments reach, and %s", name, v.placeOf(call.Pos()), why)
		}
		return ""
	}
	if arg := v.withinArg(call, fn, index); arg != nil {
		// Within an interface value is within its footprint, and within
		// an owner may be within the footprint of what it owns: memory a
		// writer may write, whatever the argument's own origin.
		if t := v.info.TypeOf(arg); t != nil {
			object, isPointer := pointee(t)
			if isIface(t) || (isPointer && v.ownsMemory(object)) {
				return fmt.Sprintf("it comes from the call of %s at %s, whose contract places it within %s, which may hold memory a writer writes", name, v.placeOf(call.Pos()), types.ExprString(arg))
			}
		}
		if why := v.memOrigin(arg, fact); why != "" {
			return fmt.Sprintf("it comes from the call of %s at %s, whose contract places it within %s, and %s", name, v.placeOf(call.Pos()), types.ExprString(arg), why)
		}
		return ""
	}
	// Within the receiver of an interface method, as what
	// (net/http.ResponseWriter).Header returns: in its footprint (F18 of
	// the review of step 5).
	if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok && fn.receiver != nil && placesWithin(fn) {
		return fmt.Sprintf("it comes from the call of %s at %s, whose contract places it within %s, which may hold memory a writer writes", name, v.placeOf(call.Pos()), types.ExprString(sel.X))
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
	if call == v.skipPollution {
		return ""
	}
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
	// The Error method of an error of known origin stores nothing
	// (errorText), and one of another origin is refused there.
	if isErrorText(v.info, call) {
		return ""
	}
	fn := v.memCallee(call)
	if fn == nil && v.literalOf(call) == nil {
		return fmt.Sprintf("the call of %s at %s has no contract that says what it stores", types.ExprString(call.Fun), v.placeOf(call.Pos()))
	}
	if fn == nil || !v.targetsHoldReferences(fn) {
		return ""
	}
	// What an entry lists under stores holds only memory the call made,
	// which lies in no row, unless it is handed something it could store.
	// A trusted call whose every target that can hold a reference lies
	// under a parameter its entry lists under stores stores there only
	// memory it made during the call (F28), and nothing else, so it stores
	// no reference of unknown origin. That memory lies in no row: a row
	// grows only by memory the methods of its value create, or, for a value
	// verified code converted, by its definition at the conversion and the
	// follow layers of stores into owned fields, and a trusted call of
	// another package is none of these; and the methods of a value from
	// code that is not verified do not write through what another call
	// stored into memory the value handed out, by the clause of What a
	// proof assumes that F33 of part 1 added.
	if fn.trust != nil && len(fn.trust.stores) > 0 && !v.targetsHold(fn, true) {
		return ""
	}
	// A callee may store memory it got other than through its arguments,
	// from its package or from a call it made (F28 of the review of step 2),
	// so a call whose targets can hold a reference pollutes, unless it is a
	// verified function that stores only what its arguments reach or new
	// memory, and is handed nothing unknown.
	if v.pkgVerifier.memSummary(fn.obj).stores && fn.trust == nil && fn.valueOf == nil && fn.methodOf == nil {
		why := v.unknownArgument(call, fact)
		if why == "" {
			return ""
		}
		return fmt.Sprintf("the call of %s at %s may store what it is handed into memory it may modify, and %s",
			types.ExprString(call.Fun), v.placeOf(call.Pos()), why)
	}
	return fmt.Sprintf("the call of %s at %s may store into memory it may modify a reference to memory of any origin",
		types.ExprString(call.Fun), v.placeOf(call.Pos()))
}

// unknownArgument returns why an argument of a call that holds memory, or
// its receiver, may be unknown, or "".
func (v *fnVerifier) unknownArgument(call *ast.CallExpr, fact memFact) string {
	operands := slices.Clone(call.Args)
	if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok && v.info.Selections[sel] != nil {
		operands = append(operands, sel.X)
	}
	for _, arg := range operands {
		if why := v.memOrigin(arg, fact); why != "" {
			return fmt.Sprintf("%s is handed %s, and %s", types.ExprString(call.Fun), types.ExprString(arg), why)
		}
	}
	return ""
}

// memSummary says of a verified function of the package or of another
// whether every result that holds memory is new or reached from its
// arguments, and whether it stores only such memory. It is a property of
// the body, decided by the same rules from the function's own parameters,
// and is the greatest fixed point over the functions of the package: a
// verified function ends, so what holds of every call it makes holds by
// induction on the depth of calls. A trusted function, a call through a
// value, and a generic function have no summary.
type memSummary struct{ results, stores bool }

// memSummary returns the summary of a function. The first time it is asked,
// it computes the summary of every verified function of the package: each
// starts true, and is decided again from its body until none changes. A
// function of another package has the summary its contract fact carries
// when it was verified; anything else has none.
func (pv *pkgVerifier) memSummary(obj *types.Func) memSummary {
	origin := pv.originOf(obj)
	if pv.summaries == nil {
		pv.summaries = map[*types.Func]memSummary{}
		var local []*funcInfo
		for _, fn := range pv.order {
			if fn.annotated() && fn.decl != nil && fn.decl.Body != nil && fn.trust == nil && !isGeneric(fn.obj) {
				local = append(local, fn)
				pv.summaries[fn.obj] = memSummary{results: true, stores: true}
			}
		}
		for changed := true; changed; {
			changed = false
			for _, fn := range local {
				next := pv.summarize(fn)
				if next != pv.summaries[fn.obj] {
					pv.summaries[fn.obj] = next
					changed = true
				}
			}
		}
	}
	if summary, known := pv.summaries[origin]; known {
		return summary
	}
	if fn := pv.contractOf(origin); fn != nil && fn.imported != nil && fn.imported.Verified {
		return memSummary{results: fn.imported.DerivedResults, stores: fn.imported.DerivedStores}
	}
	return memSummary{}
}

// summarize decides the summary of one verified function of the package
// from its body, with what is known now of its callees.
func (pv *pkgVerifier) summarize(fn *funcInfo) (summary memSummary) {
	// A body that uses Go the verifier refuses has no summary; its own
	// verification reports it.
	defer func() {
		if r := recover(); r != nil {
			switch r.(type) {
			case unsupported, abort:
				summary = memSummary{}
			default:
				panic(r)
			}
		}
	}()
	sv := pv.newVerifier(fn)
	sv.boxed = sv.findBoxed(fn.decl.Body)
	sv.classifyLiterals()
	loose := sv.memOrigins().loose
	results := true
	ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			// Its returns are its own.
			return false
		case *ast.ReturnStmt:
			if len(n.Results) == 0 {
				for _, result := range fn.results {
					if loose.unknown[result] != "" && holdsMemory(result.Type()) {
						results = false
					}
				}
			}
			for _, e := range n.Results {
				if len(n.Results) == 1 && len(fn.results) > 1 {
					for j := range fn.results {
						if sv.memResult(e, j, loose) != "" {
							results = false
						}
					}
					continue
				}
				if sv.memOrigin(e, loose) != "" {
					results = false
				}
			}
		}
		return true
	})
	// Named results that a deferred literal assigns are judged anywhere.
	for _, result := range fn.results {
		if loose.unknown[result] != "" && holdsMemory(result.Type()) {
			results = false
		}
	}
	return memSummary{results: results, stores: loose.polluted == ""}
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
	return v.targetsHold(fn, false)
}

// targetsHold is targetsHoldReferences, leaving out, when unstored is set,
// the targets under parameters that the entry lists under stores.
func (v *fnVerifier) targetsHold(fn *funcInfo, unstored bool) bool {
	view := v.viewOf(fn)
	if view.cut {
		return false
	}
	stored := map[string]bool{}
	if unstored && fn.trust != nil {
		for _, name := range fn.trust.stores {
			stored[name.text] = true
		}
	}
	for _, m := range view.fn.modifies {
		if stored[m.name] {
			continue
		}
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
		// The callee assumes the footprint of a parameter, and of what a
		// parameter that owns memory owns, apart from its other
		// parameters (enterReaches).
		param := t.param
		if t.part {
			param = t.ownerParam
		}
		// And the footprint of p.Body apart from what p and the others
		// reach: the argument for p.Body must be the caller's own p.Body,
		// listed by it, and what is passed as p outside and the caller
		// clean (F28).
		var field string
		if t.fp && param == nil && t.mod < len(fn.modifies) {
			if root := v.notWrittenRoot(fn, fn.modifies[t.mod]); root != nil {
				param, field = root, fn.modifies[t.mod].steps[0].field
			}
		}
		if !t.fp || param == nil {
			continue
		}
		if field != "" {
			body := &ast.SelectorExpr{X: passedExpr[param], Sel: &ast.Ident{Name: field}}
			shown := passed[param]
			if strings.HasPrefix(shown, "&") || strings.HasPrefix(shown, "*") {
				shown = "(" + shown + ")"
			}
			lead := fmt.Sprintf("the footprint of what is passed to %s as %s.%s may hold memory that the arguments reach, and %s relies on it not doing so",
				name, shown, field, name)
			if passedExpr[param] == nil || !v.ownFieldFootprint(body) {
				v.report(call.Pos(), "%s: %s.%s is not a field of a parameter whose %s %s's own Modifies lists as %s.%s, so nothing places it",
					lead, shown, field, field, v.fn.obj.Name(), shown, field)
				continue
			}
			fact, placed := v.memFactAt(call)
			if !placed {
				v.unsupported(call.Pos(), lead+"; a caller of a function value or a method of an interface value does not show it")
			}
			for _, other := range fn.params {
				if args[other] == nil || !holdsMemory(other.Type()) {
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
			continue
		}
		what := "the footprint of what is passed to %s as %s"
		if t.part {
			what = "the footprint of what is owned by what is passed to %s as %s"
		}
		for _, other := range fn.params {
			if other == param || args[other] == nil || !holdsMemory(other.Type()) {
				continue
			}
			lead := fmt.Sprintf(what+" may hold memory that what is passed as %s reaches, and %s relies on it not doing so",
				name, passed[param], passed[other], name)
			fact, placed := v.memFactAt(call)
			if !placed {
				v.unsupported(call.Pos(), lead+"; a caller of a function value or a method of an interface value does not show it")
			}
			// A pointer converted here: its footprint is the struct it
			// points to, and only what can refer to a value of its type
			// reaches it (F21).
			if given, object := v.convertedPointer(passedExpr[param]); object != nil && !t.part && isIface(param.Type()) {
				// The footprint of a converted owner is its struct and what
				// it owns, which a value of the type of an owned field can
				// be (F37 of the review of step 4).
				owners := map[types.Type]bool{}
				collectOwners(types.NewPointer(object), owners, map[types.Type]bool{})
				if part := ownerHolding(owners, other.Type()); part != nil {
					v.report(call.Pos(), "%s: the footprint of %s is the struct that %s points to and what it owns, which a value of type %s can be part of",
						lead, passed[param], given, types.TypeString(other.Type(), types.RelativeTo(v.pass.Pkg)))
					continue
				}
				if typeReaches(other.Type(), object, map[string]bool{}) {
					v.report(call.Pos(), "%s: the footprint of %s is the struct that %s points to, which a value of type %s can refer to",
						lead, passed[param], given, types.TypeString(other.Type(), types.RelativeTo(v.pass.Pkg)))
				}
				continue
			}
			// An owner of the project that the function made, or got as new
			// from a call, and that nothing else refers to, is placed: by
			// HI, what it owns is reached only through it (F40 of the
			// review of step 5, decided by the orchestrator).
			ownerPlaced, why := false, ""
			if t.part && t.sourcePart {
				ownerPlaced, why = v.placedOwner(call, passedExpr[param])
			}
			if !ownerPlaced && !v.placedFootprint(passedExpr[param], 0) {
				if why != "" {
					v.report(call.Pos(), "%s: %s", lead, why)
					continue
				}
				if t.part && t.sourcePart {
					v.report(call.Pos(), "%s: %s is not a parameter whose footprint %s's own Modifies lists, a value made from such parameters by a call "+
						"whose contract says so with fresh(result, w), or an owner made here or returned new by a call, so nothing places it",
						lead, passed[param], v.fn.obj.Name())
					continue
				}
				v.report(call.Pos(), "%s: %s is not a parameter whose footprint %s's own Modifies lists, or a value made from such parameters by a call "+
					"whose contract says so with fresh(result, w), so nothing places it", lead, passed[param], v.fn.obj.Name())
				continue
			}
			if ownerPlaced {
				// What else the call is handed must be no part of an owner,
				// since the row of a new owner's interface value is reached
				// only through it.
				if why := v.insideOperand(call, passedExpr[other]); why != "" {
					v.report(call.Pos(), "%s: %s", lead, why)
					continue
				}
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
	return slices.ContainsFunc(v.reaches, func(r separation) bool { return r.param == variable && r.field == "" })
}

// ownFieldFootprint reports whether an expression p.f names the footprint
// of a field of a parameter that the function lists as p.f, which a
// notWrittenBy declaration covers (F28): the caller assumes it apart from
// what p and the other parameters reach, and verified code does not store
// into the field.
func (v *fnVerifier) ownFieldFootprint(e ast.Expr) bool {
	sel, ok := ast.Unparen(e).(*ast.SelectorExpr)
	if !ok {
		return false
	}
	id, ok := ast.Unparen(sel.X).(*ast.Ident)
	if !ok {
		return false
	}
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	if variable == nil || v.findReassigned(v.bodyOrigin())[variable] {
		return false
	}
	return slices.ContainsFunc(v.reaches, func(r separation) bool { return r.param == variable && r.field == sel.Sel.Name })
}

// placedFootprint reports whether the footprint of an argument is placed:
// it is a parameter whose footprint the function lists (ownFootprint), or a
// variable assigned once, where it is declared, from a call whose contract
// says that what its result refers to is new or lies in the footprints of
// arguments that are placed in turn, as bufio.NewWriter(w) and log.New(w,
// ...) say with fresh(result, w): the fourth case of the proof at a call.
// What the call made is new, and another argument can reach it only
// through a reference to the result, which is of unknown origin, so a store
// of it pollutes the function, which the proof requires it is not. The
// variable's address is never taken, so nothing else assigns it. depth
// stops a chain that the shipped contracts cannot make.
func (v *fnVerifier) placedFootprint(e ast.Expr, depth int) bool {
	if e == nil || depth > 8 {
		return false
	}
	// A conversion between interfaces keeps the value, so its home and its
	// footprint (F28).
	if call, ok := ast.Unparen(e).(*ast.CallExpr); ok && len(call.Args) == 1 {
		if tv := v.info.Types[call.Fun]; tv.IsType() && isIface(tv.Type) && isIface(v.info.TypeOf(call.Args[0])) {
			return v.placedFootprint(call.Args[0], depth+1)
		}
	}
	if v.ownFootprint(e) {
		return true
	}
	id, ok := ast.Unparen(e).(*ast.Ident)
	if !ok {
		return false
	}
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	if variable == nil || variable.IsField() || v.boxed[variable] || v.findReassigned(v.bodyOrigin())[variable] || v.memOrigins().litAssigned[variable] {
		return false
	}
	init := v.declaredFrom(variable)
	call, isCall := ast.Unparen(init).(*ast.CallExpr)
	if !isCall {
		return false
	}
	if method, value := throughValue(v.info, call); value || method != nil || v.literalOf(call) != nil {
		return false
	}
	callee := v.pkgVerifier.calleeAt(call)
	if callee == nil {
		return false
	}
	fn := v.contractOf(callee)
	sig, isSig := callee.Type().(*types.Signature)
	if fn == nil || !isSig || sig.Results().Len() != 1 {
		return false
	}
	bound, ok := bindArgs(v.info, call, paramsOf(sig), sig.Variadic())
	if !ok {
		return false
	}
	found := false
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			if conjunct.Kind != logic.NCall || conjunct.Name != "fresh" || len(conjunct.Kids) < 2 ||
				conjunct.Kids[0].Kind != logic.NIdent || conjunct.Kids[0].Name != spelledResult(fn, 0) {
				continue
			}
			placed := true
			for _, kid := range conjunct.Kids[1:] {
				for _, arg := range bound {
					if kid.Kind != logic.NIdent || arg.param.Name() != kid.Name {
						continue
					}
					switch {
					case arg.spread:
						placed = false
					case arg.packed:
						for _, each := range arg.pack {
							placed = placed && v.placedFootprint(each, depth+1)
						}
					default:
						placed = placed && v.placedFootprint(arg.expr, depth+1)
					}
				}
			}
			found = found || placed
		}
	}
	return found
}

// declaredFrom returns the expression a local variable is given where it is
// declared, as in x := f(w) or var x = f(w), or nil.
func (v *fnVerifier) declaredFrom(variable *types.Var) ast.Expr {
	var init ast.Expr
	ast.Inspect(v.bodyOrigin(), func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.AssignStmt:
			if n.Tok == token.DEFINE && len(n.Lhs) == len(n.Rhs) {
				for i, lhs := range n.Lhs {
					if id, ok := lhs.(*ast.Ident); ok && v.info.Defs[id] == variable {
						init = n.Rhs[i]
					}
				}
			}
		case *ast.ValueSpec:
			if len(n.Names) == len(n.Values) {
				for i, name := range n.Names {
					if v.info.Defs[name] == variable {
						init = n.Values[i]
					}
				}
			}
		}
		return init == nil
	})
	return init
}

// convertedPointer returns the pointer an argument converts to an
// interface value, as written, and the type it points to, when the
// argument is a pointer written where an interface value is wanted, an
// explicit conversion of one, or a variable declared from either and never
// assigned again. The footprint of the interface value is then the struct
// the pointer pointed to at the conversion, wherever it lies, and only a
// value that can refer to a value of its type reaches it.
func (v *fnVerifier) convertedPointer(e ast.Expr) (string, types.Type) {
	if e == nil {
		return "", nil
	}
	e = ast.Unparen(e)
	if id, ok := e.(*ast.Ident); ok && isIface(v.info.TypeOf(id)) {
		variable, _ := v.info.ObjectOf(id).(*types.Var)
		if variable == nil || variable.IsField() || v.boxed[variable] || v.findReassigned(v.bodyOrigin())[variable] || v.memOrigins().litAssigned[variable] {
			return "", nil
		}
		if init := v.declaredFrom(variable); init != nil {
			return v.convertedPointer(init)
		}
		return "", nil
	}
	if call, ok := e.(*ast.CallExpr); ok && len(call.Args) == 1 {
		if tv, known := v.info.Types[call.Fun]; known && tv.IsType() && isIface(tv.Type) {
			return v.convertedPointer(call.Args[0])
		}
	}
	if object, isPointer := pointee(v.info.TypeOf(e)); isPointer {
		return types.ExprString(e), object
	}
	return "", nil
}

// typeReaches reports whether what a value of type from refers to, without
// going through an interface value or a function value, can overlap memory
// that holds a value of type target: through a pointer, a slice, a map, or
// an atomic.Pointer, at any depth, to memory that holds a target inline or
// lies inline in one, as a *Inner points into an Outer that holds an Inner
// (F41 of the review of step 5), with types the same when Go converts
// pointers between them (holdsInline). It stops
// where the assumption it proves stops: a callee assumes its footprint
// apart only from what its other parameters reach without going through an
// interface value (reachesType), so what an interface value holds is no
// part of it.
func typeReaches(from, target types.Type, seen map[string]bool) bool {
	key := typeKey(from)
	if seen[key] {
		return false
	}
	seen[key] = true
	if held, replaced := heldAs(from); replaced {
		return held != nil && typeReaches(held, target, seen)
	}
	// A pointer may point to a value that holds the struct, or into the
	// struct, at a field or an element. A slice's array may hold the
	// struct, or be an array the struct holds, which s.a[:] makes of a
	// field a, but never a field that is not an array. What a map or a
	// channel holds lies in memory of its own that no pointer reaches, so
	// they only lead on to what their keys and values refer to.
	switch u := from.Underlying().(type) {
	case *types.Basic:
		return u.Kind() == types.UnsafePointer
	case *types.Pointer:
		return holdsInline(u.Elem(), target, map[string]bool{}) || holdsInline(target, u.Elem(), map[string]bool{}) || typeReaches(u.Elem(), target, seen)
	case *types.Slice:
		return holdsInline(u.Elem(), target, map[string]bool{}) || holdsArrayInline(target, u.Elem(), map[string]bool{}) || typeReaches(u.Elem(), target, seen)
	case *types.Map:
		return typeReaches(u.Key(), target, seen) || typeReaches(u.Elem(), target, seen)
	case *types.Chan:
		return typeReaches(u.Elem(), target, seen)
	case *types.Array:
		return typeReaches(u.Elem(), target, seen)
	case *types.Struct:
		for field := range u.Fields() {
			if typeReaches(field.Type(), target, seen) {
				return true
			}
		}
	}
	return false
}

// holdsInline reports whether a value of type t is, or holds in its own
// memory as a field or an element at any depth, a value of type target.
// Two types are the same here when their underlying types are, apart from
// struct tags: Go converts a pointer to one into a pointer to the other, as
// (*Twin)(o) converts a *Outer.
func holdsInline(t, target types.Type, seen map[string]bool) bool {
	if typeKey(t.Underlying()) == typeKey(target.Underlying()) {
		return true
	}
	if seen[typeKey(t)] {
		return false
	}
	seen[typeKey(t)] = true
	if _, replaced := heldAs(t); replaced {
		return false
	}
	switch u := t.Underlying().(type) {
	case *types.Array:
		return holdsInline(u.Elem(), target, seen)
	case *types.Struct:
		for field := range u.Fields() {
			if holdsInline(field.Type(), target, seen) {
				return true
			}
		}
	}
	return false
}

// holdsArrayInline reports whether a value of type t holds in its own
// memory, at any depth, an array whose elements have type elem, with types
// the same as holdsInline takes them.
func holdsArrayInline(t, elem types.Type, seen map[string]bool) bool {
	if seen[typeKey(t)] {
		return false
	}
	seen[typeKey(t)] = true
	if _, replaced := heldAs(t); replaced {
		return false
	}
	switch u := t.Underlying().(type) {
	case *types.Array:
		return typeKey(u.Elem().Underlying()) == typeKey(elem.Underlying()) || holdsArrayInline(u.Elem(), elem, seen)
	case *types.Struct:
		for field := range u.Fields() {
			if holdsArrayInline(field.Type(), elem, seen) {
				return true
			}
		}
	}
	return false
}
