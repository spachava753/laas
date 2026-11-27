package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"
	"unicode"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A recursive local closure is a function literal assigned to a variable
// that its own body calls, as a depth-first search is written:
//
//	var visit func(node string)
//	// @Requires seen != nil
//	// @Modifies seen
//	// @Variant |g \ seen|
//	visit = func(node string) { ... visit(e) ... }
//
// A literal used in place cannot call itself, since its variable is not in
// scope inside it, and verifying it at each call would not end. Such a
// closure is verified once instead, as a function of its own, against the
// contract written directly above its assignment, and every call of it, from
// the function around it and from itself, is a call of that contract. The
// variables it captures are its inputs: each call passes their values at
// the call, and in the body they are values of their types that only its
// Requires constrains, so no fact of the place where the closure is made
// reaches it and it means the same on every path that reaches it. A captured
// variable that its body assigns is an output as well: a call hands back a
// new value, which its Ensures speaks of as x'. The closure must list such a
// variable under Modifies, where an entry also covers what a parameter of
// its type would.
//
// Only one form is recognised: a declaration var v T with no value, of an
// unnamed function type, followed directly in the same block by the one
// assignment v = func..., with every other use of v the function of a call,
// inside the literal or after the assignment. The assignment then runs
// before any call of v, so no call finds v nil. Calls of v resolve, in the
// package's copy of the type information, to a function object of the
// closure's own, so that every analysis treats them as static calls of a
// function whose contract is the closure's.

// recClosure is a recursive local closure of the package.
type recClosure struct {
	outer    *ast.FuncDecl
	variable *types.Var
	decl     *ast.DeclStmt
	assign   *ast.AssignStmt
	lit      *ast.FuncLit
	// window is where its contract stands: from the end of the statement
	// before the assignment to the assignment.
	windowStart token.Pos
	// declWindow is the stretch above the declaration, where a contract
	// would be misplaced.
	declStart token.Pos
	// obj is the function object calls of the variable resolve to, and fn
	// its contract.
	obj *types.Func
	fn  *funcInfo
	// captured are the variables of the function around it that the body
	// uses, and outputs those of them it assigns, each at the first place
	// it is assigned.
	captured []*types.Var
	outputs  []*types.Var
	assigned map[*types.Var]token.Pos
	// args names each captured variable for the analyses that root what a
	// call writes at an argument written in the source.
	args map[*types.Var]*ast.Ident
	// refused says why the closure cannot be verified, at refusedAt; the
	// function around it reports it.
	refused   string
	refusedAt token.Pos
	// listed holds the captured variables its Modifies names as a whole.
	listed map[*types.Var]bool
	// outputMods holds the indices of the Modifies entries that name an
	// output, which are needed for the assignment whatever they cover.
	outputMods map[int]bool
}

// closureName is how a diagnostic names a closure.
func closureName(variable *types.Var) string { return "the closure " + variable.Name() }

// findClosures recognises the recursive closures of a function declaration.
func (pv *pkgVerifier) findClosures(fd *ast.FuncDecl) {
	if fd.Body == nil {
		return
	}
	var lists [][]ast.Stmt
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.BlockStmt:
			lists = append(lists, n.List)
		case *ast.CaseClause:
			lists = append(lists, n.Body)
		case *ast.CommClause:
			lists = append(lists, n.Body)
		}
		return true
	})
	for _, list := range lists {
		for i, s := range list {
			ds, ok := s.(*ast.DeclStmt)
			if !ok {
				continue
			}
			gen, ok := ds.Decl.(*ast.GenDecl)
			if !ok || gen.Tok != token.VAR || len(gen.Specs) != 1 {
				continue
			}
			spec := gen.Specs[0].(*ast.ValueSpec)
			if len(spec.Names) != 1 || len(spec.Values) != 0 {
				continue
			}
			variable, _ := pv.info.Defs[spec.Names[0]].(*types.Var)
			if variable == nil {
				continue
			}
			if _, unnamed := variable.Type().(*types.Signature); !unnamed {
				continue
			}
			// The assignment is the next statement that names the variable.
			for j := i + 1; j < len(list); j++ {
				as, isAssign := list[j].(*ast.AssignStmt)
				if isAssign && as.Tok == token.ASSIGN && len(as.Lhs) == 1 && len(as.Rhs) == 1 {
					id, isIdent := ast.Unparen(as.Lhs[0]).(*ast.Ident)
					lit, isLit := ast.Unparen(as.Rhs[0]).(*ast.FuncLit)
					if isIdent && isLit && pv.info.Uses[id] == variable {
						rc := &recClosure{outer: fd, variable: variable, decl: ds, assign: as, lit: lit,
							windowStart: list[j-1].End(), declStart: ds.Pos()}
						if i > 0 {
							rc.declStart = list[i-1].End()
						} else {
							rc.declStart = enclosingStart(fd.Body, ds)
						}
						pv.closures = append(pv.closures, rc)
						break
					}
				}
				if mentions(pv.info, list[j], variable) {
					break
				}
			}
		}
	}
}

// enclosingStart returns where the stretch of comments above the first
// statement of a list begins: the opening of the block or clause that holds
// it.
func enclosingStart(body *ast.BlockStmt, s ast.Stmt) token.Pos {
	start := body.Lbrace
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.BlockStmt:
			if len(n.List) > 0 && n.List[0] == s {
				start = n.Lbrace
			}
		case *ast.CaseClause:
			if len(n.Body) > 0 && n.Body[0] == s {
				start = n.Colon
			}
		case *ast.CommClause:
			if len(n.Body) > 0 && n.Body[0] == s {
				start = n.Colon
			}
		}
		return true
	})
	return start
}

// mentions reports whether a node uses a variable.
func mentions(info *types.Info, n ast.Node, variable *types.Var) bool {
	found := false
	ast.Inspect(n, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok && info.Uses[id] == variable {
			found = true
		}
		return !found
	})
	return found
}

// closureAt returns the closure whose contract a clause in a body belongs
// to, or nil; and, for a clause above the declaration of a closure's
// variable instead, that closure as misplaced.
func (pv *pkgVerifier) closureAt(pos token.Pos) (rc, misplaced *recClosure) {
	for _, c := range pv.closures {
		if pos > c.windowStart && pos < c.assign.Pos() {
			return c, nil
		}
		if pos > c.declStart && pos < c.decl.Pos() {
			misplaced = c
		}
	}
	return nil, misplaced
}

// prepareClosures makes the contract of every closure found, before the
// annotations are placed, so that those above an assignment can join it.
func (pv *pkgVerifier) prepareClosures() {
	for _, rc := range pv.closures {
		if rc.fn != nil {
			continue
		}
		sig := pv.info.TypeOf(rc.lit).(*types.Signature)
		rc.obj = types.NewFunc(rc.lit.Pos(), pv.pass.Pkg, closureName(rc.variable), sig)
		fn := newFuncInfo(rc.obj)
		fn.decl = &ast.FuncDecl{Name: &ast.Ident{NamePos: rc.lit.Pos(), Name: rc.obj.Name()}, Type: rc.lit.Type, Body: rc.lit.Body}
		fn.closure = rc
		fn.ownParams = map[string]*types.Var{}
		for _, param := range fn.params {
			fn.ownParams[param.Name()] = param
		}
		rc.fn = fn
	}
}

// finishClosures completes the closures of the functions that are
// verified, once every annotation is placed: what each captures and
// assigns, the uses that refuse it, and the copy of the type information
// in which its calls resolve to its function object. A closure of a
// function that is not verified stays a function literal used as a value.
func (pv *pkgVerifier) finishClosures() {
	if len(pv.closures) == 0 {
		return
	}
	outerOf := map[*ast.FuncDecl]*funcInfo{}
	for _, fn := range pv.order {
		outerOf[fn.decl] = fn
	}
	var kept []*recClosure
	for _, rc := range pv.closures {
		outer := outerOf[rc.outer]
		if outer == nil || !outer.annotated() {
			if fn := rc.fn; len(fn.requires)+len(fn.ensures)+len(fn.modifies) > 0 || fn.measure != nil {
				pv.report(rc.assign.Pos(), "%s has a contract, but %s around it is not verified, so nothing reads it; annotate %s",
					closureName(rc.variable), rc.outer.Name.Name, rc.outer.Name.Name)
			}
			continue
		}
		kept = append(kept, rc)
	}
	pv.closures = kept
	if len(kept) == 0 {
		return
	}
	info := *pv.info
	info.Uses = maps.Clone(pv.info.Uses)
	info.Defs = maps.Clone(pv.info.Defs)
	pv.closureOf = map[*types.Func]*recClosure{}
	pv.closureAssigns = map[*ast.AssignStmt]*recClosure{}
	pv.closureVars = map[*types.Var]*recClosure{}
	for _, rc := range kept {
		pv.classifyClosure(rc, &info)
		pv.closureOf[rc.obj] = rc
		pv.closureAssigns[rc.assign] = rc
		pv.closureVars[rc.variable] = rc
		info.Defs[rc.fn.decl.Name] = rc.obj
		pv.funcs[rc.obj] = rc.fn
	}
	pv.info = &info
	// Each closure is verified after the function around it.
	var order []*funcInfo
	for _, fn := range pv.order {
		order = append(order, fn)
		for _, rc := range kept {
			if rc.outer == fn.decl {
				order = append(order, rc.fn)
			}
		}
	}
	pv.order = order
}

// classifyClosure finds what a closure captures and assigns and how its
// variable is used, and resolves its calls to its function object.
func (pv *pkgVerifier) classifyClosure(rc *recClosure, info *types.Info) {
	refuse := func(pos token.Pos, format string, args ...any) {
		if rc.refused == "" {
			rc.refused, rc.refusedAt = fmt.Sprintf(format, args...), pos
		}
	}
	name := rc.variable.Name()
	if rc.fn.obj.Type().(*types.Signature).Variadic() {
		refuse(rc.lit.Pos(), "%s is variadic, and a recursive closure that is variadic is not supported yet", closureName(rc.variable))
	}
	// A closure nested in another function literal is supported only where
	// that literal runs in place.
	inPlace := map[*ast.FuncLit]bool{}
	bound, _ := literalUses(pv.info, rc.outer.Body)
	for _, lit := range bound {
		inPlace[lit] = true
	}
	ast.Inspect(rc.outer.Body, func(n ast.Node) bool {
		if call, ok := n.(*ast.CallExpr); ok {
			if lit, ok := ast.Unparen(call.Fun).(*ast.FuncLit); ok {
				inPlace[lit] = true
			}
		}
		return true
	})
	ast.Inspect(rc.outer.Body, func(n ast.Node) bool {
		lit, ok := n.(*ast.FuncLit)
		if !ok || lit == rc.lit || lit.Pos() > rc.decl.Pos() || lit.End() < rc.assign.End() {
			return true
		}
		switch {
		case slices.ContainsFunc(pv.closures, func(other *recClosure) bool { return other.lit == lit }):
			refuse(rc.decl.Pos(), "%s is declared inside another recursive closure, which is not supported yet; declare it in the function around them",
				closureName(rc.variable))
		case !inPlace[lit]:
			refuse(rc.decl.Pos(), "%s is declared inside a function literal used as a value or handed to a function, which is not supported yet; "+
				"declare it in the function", closureName(rc.variable))
		}
		return true
	})
	// Every use of the variable but the assignment is the function of a
	// call, inside the literal or after the assignment, and neither
	// deferred nor run on a goroutine.
	var stack []ast.Node
	ast.Inspect(rc.outer.Body, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		stack = append(stack, n)
		id, ok := n.(*ast.Ident)
		if !ok || pv.info.Uses[id] != rc.variable {
			return true
		}
		if len(rc.assign.Lhs) == 1 && ast.Unparen(rc.assign.Lhs[0]) == id {
			return true
		}
		var parent, grand ast.Node
		for i := len(stack) - 2; i >= 0; i-- {
			if _, paren := stack[i].(*ast.ParenExpr); paren {
				continue
			}
			if parent == nil {
				parent = stack[i]
				continue
			}
			grand = stack[i]
			break
		}
		call, isCall := parent.(*ast.CallExpr)
		inside := id.Pos() >= rc.lit.Pos() && id.Pos() < rc.lit.End()
		switch {
		case !isCall || ast.Unparen(call.Fun) != id:
			switch p := parent.(type) {
			case *ast.AssignStmt:
				if slices.ContainsFunc(p.Lhs, func(e ast.Expr) bool { return ast.Unparen(e) == id }) {
					refuse(id.Pos(), "%s is assigned again; a recursive closure is assigned once, directly after its declaration", name)
					return true
				}
			case *ast.UnaryExpr:
				if p.Op == token.AND {
					refuse(id.Pos(), "the address of %s is taken; a recursive closure may only be called", name)
					return true
				}
			}
			refuse(id.Pos(), "%s holds a recursive closure and is used here other than by calling it; a recursive closure may only be called, "+
				"so it cannot be copied, passed, returned, stored, or compared; to use a function as a value, declare a named function type with a contract",
				name)
		case !inside && id.Pos() < rc.assign.End():
			refuse(id.Pos(), "%s is called before it is assigned, where it is nil; two closures that call each other are not supported yet", name)
		default:
			if _, isDefer := grand.(*ast.DeferStmt); isDefer {
				refuse(id.Pos(), "a call of the recursive closure %s is deferred, which is not supported yet; call it", name)
			}
			if _, isGo := grand.(*ast.GoStmt); isGo {
				refuse(id.Pos(), "the recursive closure %s is run on a goroutine, which is not supported", name)
			}
			info.Uses[id] = rc.obj
		}
		return true
	})
	// What the body uses of the function around it, and what it assigns.
	outside := func(variable *types.Var) bool {
		return variable != nil && variable != rc.variable && !variable.IsField() && variable.Pkg() == pv.pass.Pkg &&
			variable.Parent() != pv.pass.Pkg.Scope() && (variable.Pos() < rc.lit.Pos() || variable.Pos() >= rc.lit.End())
	}
	seen := map[*types.Var]bool{}
	rc.assigned = map[*types.Var]token.Pos{}
	v := pv.newVerifier(rc.fn)
	ast.Inspect(rc.lit.Body, func(n ast.Node) bool {
		var targets []ast.Expr
		switch n := n.(type) {
		case *ast.Ident:
			variable, _ := pv.info.Uses[n].(*types.Var)
			if !outside(variable) || seen[variable] {
				break
			}
			seen[variable] = true
			if slices.ContainsFunc(pv.closures, func(other *recClosure) bool { return other.variable == variable }) {
				refuse(n.Pos(), "%s calls %s, another recursive closure, which is not supported yet", closureName(rc.variable), closureName(variable))
				break
			}
			rc.captured = append(rc.captured, variable)
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
			if variable := v.assignedLocal(target); outside(variable) {
				if _, known := rc.assigned[variable]; !known {
					rc.assigned[variable] = target.Pos()
					rc.outputs = append(rc.outputs, variable)
				}
			}
		}
		return true
	})
	// So is a variable its contract names, which a call passes as it is.
	if scope := pv.scopeAt(rc.assign.Pos()); scope != nil {
		clauses := slices.Concat(rc.fn.requires, rc.fn.ensures)
		if rc.fn.measure != nil {
			clauses = append(clauses, rc.fn.measure)
		}
		var words []string
		for _, c := range clauses {
			words = append(words, strings.FieldsFunc(c.text, func(r rune) bool { return !unicode.IsLetter(r) && !unicode.IsDigit(r) && r != '_' })...)
		}
		for _, m := range rc.fn.modifies {
			words = append(words, m.name)
		}
		for _, word := range words {
			if _, own := rc.fn.paramNames[word]; own {
				continue
			}
			if _, own := rc.fn.resultNames[word]; own {
				continue
			}
			if _, obj := scope.LookupParent(word, rc.assign.Pos()); obj != nil {
				if variable, ok := obj.(*types.Var); ok && outside(variable) && !seen[variable] {
					seen[variable] = true
					rc.captured = append(rc.captured, variable)
				}
			}
		}
	}
	// A variable the body assigns is captured too, even if only assigned.
	for _, variable := range rc.outputs {
		if !seen[variable] {
			seen[variable] = true
			rc.captured = append(rc.captured, variable)
		}
	}
	slices.SortFunc(rc.captured, func(a, b *types.Var) int { return int(a.Pos() - b.Pos()) })
	slices.SortFunc(rc.outputs, func(a, b *types.Var) int { return int(a.Pos() - b.Pos()) })
	rc.args = map[*types.Var]*ast.Ident{}
	for _, variable := range rc.captured {
		if other, clash := rc.fn.paramNames[variable.Name()]; clash && other != variable {
			refuse(rc.lit.Pos(), "%s captures two variables named %s, or one with the name of its parameter; rename one", closureName(rc.variable), variable.Name())
			continue
		}
		rc.fn.params = append(rc.fn.params, variable)
		rc.fn.paramNames[variable.Name()] = variable
		rc.fn.ownParams[variable.Name()] = variable
		id := &ast.Ident{NamePos: rc.assign.Pos(), Name: variable.Name()}
		info.Uses[id] = variable
		rc.args[variable] = id
	}
	// A Modifies entry that names a captured variable as a whole lists it;
	// for one of a type that refers to no memory it lists only the
	// variable, and is no target of memory.
	rc.listed, rc.outputMods = map[*types.Var]bool{}, map[int]bool{}
	var modifies []*modTarget
	for _, m := range rc.fn.modifies {
		variable := rc.fn.paramNames[m.name]
		if variable == nil || len(m.steps) > 0 || m.behind || !slices.Contains(rc.captured, variable) {
			modifies = append(modifies, m)
			continue
		}
		rc.listed[variable] = true
		if _, assigned := rc.assigned[variable]; assigned {
			if !reachesMemoryType(variable.Type()) {
				continue
			}
			rc.outputMods[len(modifies)] = true
		}
		modifies = append(modifies, m)
	}
	rc.fn.modifies = modifies
	// The annotations in the body of the literal are the closure's own.
	if outer := pv.funcs[pv.info.Defs[rc.outer.Name].(*types.Func)]; outer != nil {
		var kept []*clause
		for _, c := range outer.body {
			if c.pos >= rc.lit.Body.Pos() && c.pos < rc.lit.Body.End() {
				rc.fn.body = append(rc.fn.body, c)
				continue
			}
			kept = append(kept, c)
		}
		outer.body = kept
	}
}

// reachesMemoryType reports whether a value of a type refers to memory: a
// pointer, slice, map, or interface value, or a struct that holds one.
func reachesMemoryType(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Pointer, *types.Slice, *types.Map, *types.Interface, *types.Signature, *types.Chan:
		return true
	case *types.Struct:
		for field := range u.Fields() {
			if reachesMemoryType(field.Type()) {
				return true
			}
		}
	case *types.Array:
		return reachesMemoryType(u.Elem())
	}
	return false
}

// checkClosure refuses, before a closure is verified, what it cannot be
// verified with: a captured variable that lives in memory, an assigned one
// that its Modifies does not list, and what the function around it found.
func (v *fnVerifier) checkClosure() {
	rc := v.fn.closure
	if rc.refused != "" {
		// The function around it reports why.
		panic(abort{})
	}
	outer := v.pkgVerifier.funcs[v.info.Defs[rc.outer.Name].(*types.Func)]
	if capturesBoxed(rc, v.pkgVerifier.newVerifier(outer).findBoxed(rc.outer.Body)) != nil {
		// The function around it reports why.
		panic(abort{})
	}
	for _, variable := range rc.outputs {
		if !rc.listed[variable] {
			v.report(rc.assigned[variable], "%s is assigned, which %s may not modify; list it in a // @Modifies clause above %s = func...",
				variable.Name(), closureName(rc.variable), rc.variable.Name())
		}
	}
}

// closureOutputs returns the values the outputs of the closure being
// verified hold in a state, for its Ensures at a return; nil for any other
// function.
func (v *fnVerifier) closureOutputs(st *state) map[*types.Var]value {
	if v.fn.closure == nil {
		return nil
	}
	outs := map[*types.Var]value{}
	for _, variable := range v.fn.closure.outputs {
		outs[variable] = v.current(st, variable)
	}
	return outs
}

// callClosure verifies a call of a recursive closure: the arguments are
// evaluated, the captured variables are passed as they are now, the
// contract is applied, and the outputs take the values it hands back.
func (v *fnVerifier) callClosure(call *ast.CallExpr, callee *types.Func, fn *funcInfo, st *state, guard []*logic.Term, operands *ceiling) []value {
	rc := fn.closure
	args := v.arguments(call, callee, st, guard)
	for _, variable := range rc.captured {
		args[variable] = v.current(st, variable)
	}
	v.unit.reach(operands)
	before := v.snapshot(st)
	v.closureOuts = nil
	results := v.invoke(call, fn, args, st, guard)
	for _, variable := range rc.outputs {
		if out := v.closureOuts[variable]; out != nil && st.vals[variable] != nil {
			st.vals[variable] = out
		}
	}
	v.closureOuts = nil
	if changed(before, v.snapshot(st)) {
		v.unit.wrote(st, "the call to "+rc.variable.Name())
	}
	return results
}

// placeInClosure binds a clause directly above the assignment of a closure
// to the closure's contract, and refuses what has no place there.
func (pv *pkgVerifier) placeInClosure(rc *recClosure, c *clause) *funcInfo {
	fn := rc.fn
	switch c.kind {
	case "Requires":
		fn.requires = append(fn.requires, c)
	case "Ensures":
		fn.ensures = append(fn.ensures, c)
	case "Modifies":
	case "Variant":
		if fn.measure != nil {
			pv.report(c.pos, "%s already has a Variant", closureName(rc.variable))
			fn.broken = true
		}
		fn.measure = c
	case "Exits":
		pv.report(c.pos, "an Exits annotation cannot stand above a recursive closure: a recursive closure may not end the process")
		fn.broken = true
	default:
		pv.report(c.pos, "%s annotation stands in the contract of %s, directly above its assignment, where only Requires, Modifies, Variant, and Ensures "+
			"belong; put it between statements", c.kind, closureName(rc.variable))
		fn.broken = true
	}
	return fn
}

// unknownOuts returns, for the contract of a recursive closure read on
// return where no call or return gives them, values of the outputs of
// which nothing is known; nil for any other contract.
func (v *fnVerifier) unknownOuts(fn *funcInfo, st *state) map[*types.Var]value {
	if fn.closure == nil {
		return nil
	}
	outs := map[*types.Var]value{}
	for _, variable := range fn.closure.outputs {
		if _, ok := layoutOf(variable.Type()); ok {
			outs[variable] = v.unknown(variable.Name(), variable.Type(), st)
		}
	}
	return outs
}

// A Variant |A \ S| counts the keys of the map A that are not keys of the
// map S: what is left to visit of a search that marks what it has seen in
// S. It decreases from one point to a later one when
//
//	(i)   every key A has later it had before,
//	(ii)  every key of A later that S had before S still has, and
//	(iii) some key that A had and S had not before is no longer in A or
//	      is now in S,
//
// since then the keys of A not in S later are among those before, less the
// key of (iii). It is a natural number, as a map has finitely many keys, so
// it rests on no bound that memory gives. No term counts it: it is never
// stated, only these goals, which read which keys the maps have.

// keysLeft is a Variant |A \ S| read at one point.
type keysLeft struct {
	env  *specEnv
	a, s pathAt
	key  types.Type
}

// pathAt is a path of a formula as an environment reads it.
type pathAt struct {
	root  string
	steps []logic.Step
	when  logic.When
}

// readKeysLeft reads a Variant of the form |A \ S| at a point, or reports
// that the clause has another form.
func (v *fnVerifier) readKeysLeft(c *clause, env *specEnv) (*keysLeft, bool) {
	if c == nil || c.node == nil || c.node.Kind != logic.NKeysLeft {
		return nil, false
	}
	var keys []types.Type
	var paths []pathAt
	for _, n := range c.node.Kids {
		root, steps, when, ok := simplePath(n)
		if !ok {
			v.misread(c, fmt.Errorf("%s in |A \\ S| must be a map reached from a variable", n))
		}
		t, _ := env.PathType(root, steps, when).(types.Type)
		if t == nil || !isMap(t) {
			v.misread(c, fmt.Errorf("%s is not a map; |A \\ S| counts the keys of the map A that are not keys of the map S", n))
		}
		key, _ := mapParts(t)
		keys = append(keys, key)
		paths = append(paths, pathAt{root, steps, when})
	}
	if !types.Identical(keys[0], keys[1]) {
		v.misread(c, fmt.Errorf("the maps of %s have keys of the types %s and %s; |A \\ S| needs maps with keys of one type", c.text, keys[0], keys[1]))
	}
	return &keysLeft{env: env, a: paths[0], s: paths[1], key: keys[0]}, true
}

// simplePath splits a path to a map into the variable it starts from, its
// fields, and the state it is read in.
func simplePath(n *logic.Node) (root string, steps []logic.Step, when logic.When, ok bool) {
	if n.Kind == logic.NCall && n.Name == "old" && len(n.Kids) == 1 {
		root, steps, _, ok = simplePath(n.Kids[0])
		return root, steps, logic.Old, ok && !n.Kids[0].Primed
	}
	switch n.Kind {
	case logic.NIdent:
		when = logic.Now
		if n.Primed {
			when = logic.Primed
		}
		return n.Name, nil, when, true
	case logic.NField:
		root, steps, when, ok = simplePath(n.Kids[0])
		if n.Primed {
			when = logic.Primed
		}
		return root, append(steps, logic.Step{Field: n.Name}), when, ok
	}
	return "", nil, logic.Now, false
}

// keysLeftDecreases is the goal that a Variant |A \ S| read later is less
// than read before, with the facts of every read noted in st.
func (v *fnVerifier) keysLeftDecreases(c *clause, before, after *keysLeft, st *state) *logic.Term {
	sort, _ := sortOf(before.key)
	n := 0
	quantified := func(exists bool, body func(k *logic.Term, has func(*keysLeft, pathAt) *logic.Term) *logic.Term) *logic.Term {
		n++
		k := logic.Bound(fmt.Sprintf("@left%d", n), sort)
		var premises []*logic.Term
		has := func(at *keysLeft, p pathAt) *logic.Term {
			env := *at.env
			env.sink = st
			env.OpenBound([]*logic.Term{k})
			t, err := env.Path(p.root, append(slices.Clip(p.steps), logic.Step{Index: k, Has: true}), p.when)
			premises = append(premises, env.CloseBound()...)
			if err != nil {
				v.misread(c, err)
			}
			return t
		}
		result := body(k, has)
		if exists {
			return logic.Exists(k, logic.And(append(premises, result)...))
		}
		return logic.Forall(k, logic.Implies(logic.And(premises...), result))
	}
	unchanged := quantified(false, func(k *logic.Term, has func(*keysLeft, pathAt) *logic.Term) *logic.Term {
		return logic.Implies(has(after, after.a), has(before, before.a))
	})
	kept := quantified(false, func(k *logic.Term, has func(*keysLeft, pathAt) *logic.Term) *logic.Term {
		return logic.Implies(logic.And(has(after, after.a), has(before, before.s)), has(after, after.s))
	})
	visited := quantified(true, func(k *logic.Term, has func(*keysLeft, pathAt) *logic.Term) *logic.Term {
		return logic.And(has(before, before.a), logic.Not(has(before, before.s)), logic.Or(logic.Not(has(after, after.a)), has(after, after.s)))
	})
	return logic.And(unchanged, kept, visited)
}

// capturesBoxed returns a variable that a closure captures and that lives
// in memory in the function around it, by boxed, or nil.
func capturesBoxed(rc *recClosure, boxed map[*types.Var]bool) *types.Var {
	for _, variable := range rc.captured {
		if boxed[variable] {
			return variable
		}
	}
	return nil
}
