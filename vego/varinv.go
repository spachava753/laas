package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"path/filepath"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Invariants of package-level variables (part 2 of package-level
// variables, O4). An Invariant in the doc comment of a var declaration
// holds of the variables of that declaration, its group: of the spec, or
// of the parenthesised block. It holds whenever no function of the package
// that touches the group runs (V3): initialisation establishes it, every
// writer is a verified function of the package that restores it on
// return, it is proved before every call that may reach a function that
// touches it, and what it reads is reached only through the group's
// variables.

// varGroup is a group of package-level variables with invariants.
type varGroup struct {
	vars    []*types.Var
	clauses []*clause
	spec    *ast.ValueSpec
	gen     *ast.GenDecl
	// refused says why the invariants cannot be used, as reported at the
	// declaration; nothing is assumed of the group then.
	refused string
	// set holds the clauses as the frame reads invariants: a set with no
	// value, whose names are the group's variables.
	set *invariantSet
}

// varDocumented returns the var declaration whose doc comment a comment
// group is, if any, with the variables it declares.
func (pv *pkgVerifier) varDocumented(file *ast.File, group *ast.CommentGroup) (*ast.GenDecl, *ast.ValueSpec, []*types.Var, bool) {
	for _, decl := range file.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.VAR {
			continue
		}
		var vars []*types.Var
		for _, spec := range gen.Specs {
			spec := spec.(*ast.ValueSpec)
			var own []*types.Var
			for _, name := range spec.Names {
				if variable, ok := pv.info.Defs[name].(*types.Var); ok {
					own = append(own, variable)
				}
			}
			if spec.Doc == group && group != nil {
				return gen, spec, own, true
			}
			vars = append(vars, own...)
		}
		if gen.Doc == group && group != nil {
			var spec *ast.ValueSpec
			if len(gen.Specs) == 1 {
				spec = gen.Specs[0].(*ast.ValueSpec)
			}
			return gen, spec, vars, true
		}
	}
	return nil, nil, nil, false
}

// addVarInvariant records an annotation written in the doc comment of a
// var declaration.
func (pv *pkgVerifier) addVarInvariant(gen *ast.GenDecl, spec *ast.ValueSpec, vars []*types.Var, c *clause) {
	if c.kind != "Invariant" {
		pv.unread = true
		pv.report(c.pos, "%s annotations do not belong on a variable; a var declaration can only have Invariant annotations", c.kind)
		return
	}
	var group *varGroup
	for _, g := range pv.varGroups {
		if g.gen == gen && g.spec == spec {
			group = g
		}
	}
	if group == nil {
		group = &varGroup{vars: vars, gen: gen, spec: spec}
		group.set = &invariantSet{owner: &funcInfo{}, group: group}
		pv.varGroups = append(pv.varGroups, group)
		if pv.groupOf == nil {
			pv.groupOf = map[*types.Var]*varGroup{}
		}
		for _, variable := range vars {
			pv.groupOf[variable] = group
		}
	}
	node, err := logic.ParseFormula(c.text)
	if err != nil {
		pv.report(c.pos, "syntax error in Invariant annotation: %v", err)
		group.refused = "an Invariant annotation could not be read"
		return
	}
	c.node = node
	group.clauses = append(group.clauses, c)
	group.set.clauses = group.clauses
}

// groupName spells the variables of a group.
func (pv *pkgVerifier) groupName(g *varGroup) string {
	names := make([]string, len(g.vars))
	for i, variable := range g.vars {
		names[i] = variable.Name()
	}
	return strings.Join(names, ", ")
}

// checkVarGroups decides, once the package is collected, whether the
// invariants of each group can be relied on, and reports at the
// declaration why not.
func (pv *pkgVerifier) checkVarGroups() {
	for _, g := range pv.varGroups {
		if g.refused != "" {
			continue
		}
		refuse := func(format string, args ...any) {
			g.refused = fmt.Sprintf(format, args...)
			pv.report(g.clauses[0].pos, "the invariant of %s cannot be relied on: %s", pv.groupName(g), g.refused)
		}
		for _, variable := range g.vars {
			switch {
			case variable.Exported():
				refuse("%s is exported, and code of another package may assign it; an invariant holds only of variables that only the package changes", variable.Name())
			case pv.changeKinds[variable]&^changeAssigned != 0 || isError(variable.Type()):
				refuse("%s", pv.assignedWhy(variable))
			case pv.reassigned[variable] && pv.assignedWhy(variable) != "":
				refuse("%s", pv.assignedWhy(variable))
			}
			if g.refused != "" {
				break
			}
		}
		if g.refused != "" {
			continue
		}
		if where := pv.unverifiedWriter(g); where != "" {
			refuse("%s; every change of a variable with an invariant must be made by a function of the package that is verified, which restores it, so call one", where)
			continue
		}
		// What a variable of the group refers to must be made by its
		// initialiser, so that nothing else held it before either.
		for _, variable := range g.vars {
			if !holdsMemory(variable.Type()) {
				continue
			}
			for _, init := range pv.info.InitOrder {
				if len(init.Lhs) == 1 && init.Lhs[0] == variable {
					if known := pv.knownOf(init.Rhs, variable.Type(), true); known.Kind != knownMade && known.Kind != knownZero && !pv.info.Types[init.Rhs].IsNil() {
						refuse("the initialiser of %s does not make what it refers to, so something else may hold it", variable.Name())
					}
				}
			}
			if g.refused != "" {
				break
			}
		}
		if g.refused != "" {
			continue
		}
		if where := pv.groupEscape(g); where != "" {
			refuse("%s, so a write through another reference could break the invariant without naming the variable", where)
			continue
		}
		// A variable of the group with an initialiser has no value before
		// it runs.
		initialised := func(variable *types.Var) bool {
			return slices.ContainsFunc(pv.info.InitOrder, func(init *types.Initializer) bool { return slices.Contains(init.Lhs, variable) })
		}
		if pv.hidden != "" && slices.ContainsFunc(g.vars, initialised) {
			refuse("%s while the variables of the package are initialised, which may run a function that assumes the invariant before it holds", pv.hidden)
		}
	}
}

// unverifiedWriter returns where a function that is not verified, or code
// outside every function, changes a variable of a group, or "".
func (pv *pkgVerifier) unverifiedWriter(g *varGroup) string {
	found := ""
	for _, file := range pv.pass.Files {
		var stack []ast.Node
		ast.Inspect(file, func(n ast.Node) bool {
			if n == nil {
				stack = stack[:len(stack)-1]
				return true
			}
			stack = append(stack, n)
			id, ok := n.(*ast.Ident)
			if !ok || found != "" {
				return true
			}
			variable, ok := pv.info.Uses[id].(*types.Var)
			if !ok || !slices.Contains(g.vars, variable) {
				return true
			}
			if use := pv.useOf(stack); use.change == "" && !pathWritten(pv.info, stack) {
				return true
			}
			var decl *ast.FuncDecl
			for i := len(stack) - 1; i >= 0 && decl == nil; i-- {
				decl, _ = stack[i].(*ast.FuncDecl)
			}
			where := pv.placeOfPos(id.Pos())
			switch {
			case decl == nil:
				found = fmt.Sprintf("%s is changed at %s outside every function", variable.Name(), where)
			case decl.Name.Name == "init" && decl.Recv == nil && !pv.annotatedDecl(decl):
				found = fmt.Sprintf("%s is changed at %s in an init function that is not verified; give it a contract, as // @Modifies %s", variable.Name(), where, variable.Name())
			case !pv.annotatedDecl(decl):
				found = fmt.Sprintf("%s is changed at %s in %s, which is not verified", variable.Name(), where, decl.Name.Name)
			}
			return true
		})
	}
	return found
}

// annotatedDecl reports whether a declared function is verified.
func (pv *pkgVerifier) annotatedDecl(decl *ast.FuncDecl) bool {
	obj, _ := pv.info.Defs[decl.Name].(*types.Func)
	fn := pv.funcs[obj]
	return fn != nil && fn.annotated()
}

// groupEscape returns where a use in the package lets a reference to what
// a variable of the group refers to out of it, or "": every use must read
// a value out of it, write through its path, or assign it.
func (pv *pkgVerifier) groupEscape(g *varGroup) string {
	found := ""
	for _, file := range pv.pass.Files {
		var stack []ast.Node
		ast.Inspect(file, func(n ast.Node) bool {
			if n == nil {
				stack = stack[:len(stack)-1]
				return true
			}
			stack = append(stack, n)
			id, ok := n.(*ast.Ident)
			if !ok || found != "" {
				return true
			}
			variable, ok := pv.info.Uses[id].(*types.Var)
			if !ok || !slices.Contains(g.vars, variable) || !holdsMemory(variable.Type()) {
				return true
			}
			use := pv.useOf(stack)
			if !use.escape || use.change == "is assigned" && pv.assignedFresh(stack) || pathWritten(pv.info, stack) || pv.handedToReader(stack) {
				return true
			}
			found = fmt.Sprintf("the use of %s at %s lets a reference to what it refers to out of it", variable.Name(), pv.placeOfPos(id.Pos()))
			return true
		})
	}
	return found
}

// assignedFresh reports whether the use at the end of stack is the whole
// target of an assignment whose value is made where it stands, so that
// nothing else refers to it.
func (pv *pkgVerifier) assignedFresh(stack []ast.Node) bool {
	if len(stack) < 2 {
		return false
	}
	assign, ok := stack[len(stack)-2].(*ast.AssignStmt)
	if !ok || len(assign.Lhs) != len(assign.Rhs) {
		return false
	}
	for i, lhs := range assign.Lhs {
		if lhs != stack[len(stack)-1] {
			continue
		}
		switch rhs := ast.Unparen(assign.Rhs[i]).(type) {
		case *ast.CompositeLit:
			return true
		case *ast.UnaryExpr:
			_, lit := ast.Unparen(rhs.X).(*ast.CompositeLit)
			return rhs.Op == token.AND && lit
		case *ast.CallExpr:
			id, ok := ast.Unparen(rhs.Fun).(*ast.Ident)
			builtin, isBuiltin := pv.info.Uses[id].(*types.Builtin)
			return ok && isBuiltin && (builtin.Name() == "make" || builtin.Name() == "new")
		case *ast.Ident:
			return pv.info.Types[rhs].IsNil()
		}
	}
	return false
}

// placeOfPos spells a position as file:line.
func (pv *pkgVerifier) placeOfPos(pos token.Pos) string {
	position := pv.pass.Fset.Position(pos)
	return fmt.Sprintf("%s:%d", filepath.Base(position.Filename), position.Line)
}

// groupsTouched returns the groups whose variables a declared function of
// the package names in its body or its contract, or that a function it may
// call does, by the call graph.
func (pv *pkgVerifier) groupsTouched(fn *funcInfo) []*varGroup {
	if len(pv.varGroups) == 0 || fn == nil || fn.obj == nil {
		return nil
	}
	if pv.touched == nil {
		pv.touched = map[*funcInfo][]*varGroup{}
		g := pv.callGraph()
		direct := map[*callNode]map[*varGroup]bool{}
		var nodes []*callNode
		for _, node := range g.byObj {
			nodes = append(nodes, node)
		}
		for _, node := range g.lits {
			nodes = append(nodes, node)
		}
		for _, node := range nodes {
			direct[node] = pv.nodeGroups(node)
		}
		pv.touchedAt = direct
		for changed := true; changed; {
			changed = false
			for _, node := range nodes {
				for _, e := range node.edges {
					for group := range direct[e.to] {
						if !direct[node][group] {
							direct[node][group] = true
							changed = true
						}
					}
				}
			}
		}
		for _, node := range nodes {
			if node.fn == nil {
				continue
			}
			for _, group := range pv.varGroups {
				if direct[node][group] && group.refused == "" {
					pv.touched[node.fn] = append(pv.touched[node.fn], group)
				}
			}
		}
	}
	if node := pv.callGraph().byObj[pv.originOf(fn.obj)]; node != nil && node.fn != nil {
		return pv.touched[node.fn]
	}
	return nil
}

// nodeGroups returns the groups whose variables a node names, in its body
// or, for a function, in the names of its contract.
func (pv *pkgVerifier) nodeGroups(node *callNode) map[*varGroup]bool {
	found := map[*varGroup]bool{}
	var body ast.Node
	switch {
	case node.lit != nil:
		body = node.lit.Body
	case node.fn != nil && node.fn.decl != nil:
		body = node.fn.decl
	}
	if body != nil {
		ast.Inspect(body, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok {
				if variable, ok := pv.info.Uses[id].(*types.Var); ok && pv.groupOf[variable] != nil {
					found[pv.groupOf[variable]] = true
				}
			}
			return true
		})
	}
	if node.fn != nil {
		names := map[string]bool{}
		for _, c := range slices.Concat(node.fn.requires, node.fn.ensures) {
			if c.node != nil {
				c.node.Walk(func(n *logic.Node) {
					if n.Kind == logic.NIdent {
						names[n.Name] = true
					}
				})
			}
		}
		for _, m := range node.fn.modifies {
			names[m.name] = true
		}
		for _, group := range pv.varGroups {
			for _, variable := range group.vars {
				if names[variable.Name()] {
					found[group] = true
				}
			}
		}
	}
	return found
}

// groupHolds returns the conjunction of the invariants of a group read in
// mem.
func (v *fnVerifier) groupHolds(g *varGroup, sink *state, mem memory) []*logic.Term {
	// Reading the invariant reads the variables; it is not the function's
	// own reading, which the note on lost contents speaks of.
	saved := v.groupReading
	v.groupReading = true
	defer func() { v.groupReading = saved }()
	env := &specEnv{v: v, sink: sink, now: mem, pos: g.clauses[0].pos}
	var terms []*logic.Term
	for _, c := range g.clauses {
		terms = append(terms, v.formula(c, c.node, env))
	}
	return terms
}

// proveGroups proves the invariants of the groups, read in the state's
// memory, where they must hold: before a call that may assume them, and on
// return of a function that may have changed them.
func (v *fnVerifier) proveGroups(st *state, guard []*logic.Term, groups []*varGroup, pos token.Pos, where string) {
	for _, g := range groups {
		// A clause is kept by frame where nothing it reads changed since a
		// point where it held, as a type's invariant is (Invariants kept by
		// frame).
		step := invariantStep{set: g.set}
		saved := v.groupReading
		v.groupReading = true
		env := v.invariantEnv(g.set, st, st.mem, nil, nil)
		for _, c := range g.clauses {
			v.checkClauseFramed(c, env, st, guard, pos, fmt.Sprintf("invariant of %s may not hold %s", v.groupName(g), where),
				func(node *logic.Node, _ *logic.Term) bool { return v.framedStep(st, step, st.mem, c, node) })
		}
		v.groupReading = saved
	}
}

// assumeGroup assumes the invariants of a group read in mem, and keeps
// where they held for a frame, when they hold with no condition.
func (v *fnVerifier) assumeGroup(st *state, guard []*logic.Term, mem memory, g *varGroup, from string) {
	for _, t := range v.groupHolds(g, st, mem) {
		st.assume(logic.Implies(logic.And(guard...), t))
	}
	if len(guard) == 0 {
		st.keep(invariantStep{set: g.set}, mem, from)
	}
}

// groupsCovered returns the groups some variable of which a list of targets
// covers.
func (v *fnVerifier) groupsCovered(targets []target, among []*varGroup) []*varGroup {
	var found []*varGroup
	for _, g := range among {
		if g.refused != "" {
			continue
		}
		for _, variable := range g.vars {
			var covers func(t target) bool
			if v.isAssigned(variable) {
				key := v.globalCells(variable)[0].key
				covers = func(t target) bool { return slices.ContainsFunc(t.cells, func(c cell) bool { return c.key == key }) }
			} else {
				// What a fixed variable refers to, at its reference.
				covers = func(t target) bool { return v.fixedVariableAt(t.ref) == variable }
			}
			if slices.ContainsFunc(targets, covers) && !slices.Contains(found, g) {
				found = append(found, g)
			}
		}
	}
	return found
}

// checkGroupsInitialised proves, for each group, that its invariants hold
// of what the declarations give its variables, before any function runs.
func (pv *pkgVerifier) checkGroupsInitialised() {
	for _, g := range pv.varGroups {
		if g.refused != "" {
			continue
		}
		pv.run(&funcInfo{obj: types.NewFunc(g.gen.Pos(), pv.pass.Pkg, "init of "+pv.groupName(g), types.NewSignatureType(nil, nil, nil, nil, nil, false))}, func(v *fnVerifier) {
			st := &state{vals: map[*types.Var]value{}, mem: memory{}, brk: logic.Const("brk", logic.Ref), noted: map[string]bool{}}
			v.entryBrk = st.brk
			st.assume(logic.Le(logic.IntLit(1), st.brk))
			// Each variable of the group holds what its initialiser
			// evaluates to, run as code, or its zero value.
			v.initStorage = map[*types.Var]bool{}
			for _, variable := range g.vars {
				v.initStorage[variable] = true
				val := zeroValue(variable.Type())
				for _, init := range pv.info.InitOrder {
					if len(init.Lhs) == 1 && init.Lhs[0] == variable {
						v.openUnit(st)
						val = v.eval(init.Rhs, st, nil)
						v.closeUnit(st)
					}
				}
				v.noteGlobal(st, variable)
				v.put(st, v.globalCells(variable), globalRef(variable), logic.IntLit(0), val)
			}
			v.groupNames = map[*types.Var]bool{}
			holds := v.groupHolds(g, st, st.mem)
			// An invariant reads only the variables of its group, and
			// variables that nothing in the build changes: a writer of any
			// other would not know to restore it (F29 of the review of
			// step 1 of part 2).
			for _, variable := range slices.SortedFunc(maps.Keys(v.groupNames), func(a, b *types.Var) int { return int(a.Pos() - b.Pos()) }) {
				_, written := pv.writtenInBuild()[errorKey(variable)]
				if !slices.Contains(g.vars, variable) && (pv.reassigned[variable] || written || pv.isAssigned(variable)) {
					g.refused = fmt.Sprintf("it names %s, which is not a variable of its group and which the build changes; declare %s in the same var declaration", v.spelling(variable), v.spelling(variable))
					pv.report(g.clauses[0].pos, "the invariant of %s cannot be relied on: %s", pv.groupName(g), g.refused)
					break
				}
			}
			v.groupNames = nil
			if g.refused != "" {
				return
			}
			for i, t := range holds {
				v.check(st, nil, t, g.clauses[i].pos, "invariant of %s may not hold when the package is initialised: %s; "+
					"it must follow from what the declarations give the variables", pv.groupName(g), g.clauses[i].text)
			}
		})
	}
}

// callGroups returns the groups whose invariants a call may assume: those a
// function of the package it calls touches, or that code it may run does,
// by the call graph.
func (v *fnVerifier) callGroups(call *ast.CallExpr, fn *funcInfo) []*varGroup {
	if len(v.varGroups) == 0 || call == nil {
		return nil
	}
	if fn.trust == nil && fn.valueOf == nil && fn.methodOf == nil && fn.obj != nil && fn.obj.Pkg() == v.pass.Pkg {
		return v.groupsTouched(fn)
	}
	v.groupsTouched(v.fn)
	var found []*varGroup
	edges := v.callEdges(call, fn)
	if fn.trust != nil {
		edges = v.callGraph().sites[call]
	}
	reached := []*callNode{}
	for _, e := range edges {
		reached = append(reached, e.to)
	}
	// A call into code of another package may run what the package let
	// out into memory it did not make (F13).
	if fn.obj == nil || fn.obj.Pkg() != v.pass.Pkg || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		reached = append(reached, v.letOut()...)
		// And every exported function and method with an exported name,
		// of which any package can make a value and keep it (F33 of the
		// review of step 2 of part 2), as the call graph says of a call
		// through a value.
		g := v.callGraph()
		for obj, node := range g.byObj {
			if obj.Exported() {
				reached = append(reached, node)
			}
		}
	}
	for _, node := range reached {
		for _, g := range v.varGroups {
			if v.touchedAt[node][g] && g.refused == "" && !slices.Contains(found, g) {
				found = append(found, g)
			}
		}
	}
	return found
}

// groupsNamed returns the groups whose variables a declared function of the
// package names, in its body or its contract.
func (pv *pkgVerifier) groupsNamed(fn *funcInfo) []*varGroup {
	if len(pv.varGroups) == 0 || fn == nil || fn.obj == nil {
		return nil
	}
	node := pv.callGraph().byObj[pv.originOf(fn.obj)]
	if node == nil {
		return nil
	}
	named := pv.nodeGroups(node)
	var found []*varGroup
	for _, g := range pv.varGroups {
		if named[g] && g.refused == "" {
			found = append(found, g)
		}
	}
	return found
}

// handedToReader reports whether the use at the end of stack is an argument
// of a call of a function that keeps nothing of it and writes nothing
// through it: a verified function whose summary keeps nothing of the
// parameter and whose Modifies does not name it, or a trusted function
// whose entry neither keeps nor modifies it. Such a callee only reads what
// the variable refers to while it runs, so the memory is still reached only
// through the variable, and a callee that writes nothing of it cannot break
// the invariant it does not know of.
func (pv *pkgVerifier) handedToReader(stack []ast.Node) bool {
	if len(stack) < 2 {
		return false
	}
	arg := stack[len(stack)-1].(ast.Expr)
	call, ok := stack[len(stack)-2].(*ast.CallExpr)
	if !ok {
		return false
	}
	index := slices.IndexFunc(call.Args, func(e ast.Expr) bool { return e == arg })
	callee := pv.calleeAt(call)
	if index < 0 || callee == nil || call.Ellipsis.IsValid() {
		return false
	}
	sig := callee.Type().(*types.Signature)
	if index >= sig.Params().Len() || sig.Variadic() && index >= sig.Params().Len()-1 {
		return false
	}
	param := sig.Params().At(index)
	fn := pv.contractOf(callee)
	switch {
	case fn == nil:
		return false
	case fn.trust != nil:
		// A result that holds memory may be any argument's, unless the
		// entry says it is new (F34 of the review of step 2 of part 2).
		for result := range sig.Results().Variables() {
			if holdsMemory(result.Type()) {
				return false
			}
		}
		return !slices.ContainsFunc(fn.trust.keeps, func(item trustKeep) bool { return item.name == param.Name() }) &&
			!slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == param.Name() })
	}
	summary := pv.ownSummaryOf(fn)
	at := slices.IndexFunc(fn.params, func(p *types.Var) bool { return p.Name() == param.Name() })
	if summary == nil || at < 0 || at >= len(summary.keeps) || summary.keeps[at] ||
		slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == param.Name() }) {
		return false
	}
	// No result may hold what the parameter refers to, or memory derived
	// from it (F34).
	for _, result := range summary.results {
		if result.unknown || slices.Contains(result.from, at) || slices.Contains(result.inside, at) {
			return false
		}
	}
	return true
}

// letOut returns the nodes of the call graph, functions, methods, and
// literals of the package, that the package lets out into memory it did
// not make: stored through a pointer, a field, or an element, or into a
// variable of another package, or handed to a function of another package
// that may keep what it is handed. Code of another package can run them
// at any later call, so a call of a function of another package counts as
// reaching each of them (F13 of the design review, F30 of the review of
// step 1 of part 2).
func (pv *pkgVerifier) letOut() []*callNode {
	if pv.letOutDone {
		return pv.letOutNodes
	}
	pv.letOutDone = true
	g := pv.callGraph()
	var found []*callNode
	add := func(e ast.Expr) {
		var visit func(e ast.Expr)
		visit = func(e ast.Expr) {
			switch x := ast.Unparen(e).(type) {
			case *ast.FuncLit:
				if node := g.lits[x]; node != nil && !slices.Contains(found, node) {
					found = append(found, node)
				}
			case *ast.Ident:
				if named, ok := pv.info.Uses[x].(*types.Func); ok && named.Pkg() == pv.pass.Pkg {
					if node := g.byObj[named.Origin()]; node != nil && !slices.Contains(found, node) {
						found = append(found, node)
					}
				}
			case *ast.SelectorExpr:
				if selection := pv.info.Selections[x]; selection != nil && selection.Kind() == types.MethodVal {
					if method, ok := selection.Obj().(*types.Func); ok && method.Pkg() == pv.pass.Pkg {
						if node := g.byObj[method.Origin()]; node != nil && !slices.Contains(found, node) {
							found = append(found, node)
						}
					}
				}
			case *ast.CompositeLit:
				for _, elt := range x.Elts {
					if kv, ok := elt.(*ast.KeyValueExpr); ok {
						elt = kv.Value
					}
					visit(elt)
				}
			case *ast.UnaryExpr:
				visit(x.X)
			}
		}
		visit(e)
	}
	intoMemory := func(lhs ast.Expr) bool {
		switch x := ast.Unparen(lhs).(type) {
		case *ast.Ident:
			variable, ok := pv.info.ObjectOf(x).(*types.Var)
			return ok && variable.Pkg() != nil && variable.Pkg() != pv.pass.Pkg && variable.Parent() == variable.Pkg().Scope()
		case *ast.SelectorExpr:
			if id, ok := x.X.(*ast.Ident); ok {
				if _, isPkg := pv.info.Uses[id].(*types.PkgName); isPkg {
					return true
				}
			}
			return true
		case *ast.IndexExpr, *ast.StarExpr:
			return true
		}
		return false
	}
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.AssignStmt:
				if len(n.Lhs) == len(n.Rhs) {
					for i, lhs := range n.Lhs {
						if intoMemory(lhs) {
							add(n.Rhs[i])
						}
					}
				}
			case *ast.CallExpr:
				callee := pv.calleeAt(n)
				if callee == nil || callee.Pkg() == pv.pass.Pkg {
					break
				}
				fn := pv.contractOf(callee)
				sig := callee.Type().(*types.Signature)
				for i, arg := range n.Args {
					keeps := fn == nil
					if fn != nil && i < sig.Params().Len() {
						name := sig.Params().At(i).Name()
						switch {
						case fn.trust != nil:
							keeps = slices.ContainsFunc(fn.trust.keeps, func(item trustKeep) bool { return item.name == name })
						default:
							summary := pv.ownSummaryOf(fn)
							at := slices.IndexFunc(fn.params, func(p *types.Var) bool { return p.Name() == name })
							keeps = summary == nil || at < 0 || at >= len(summary.keeps) || summary.keeps[at]
						}
					}
					if keeps {
						add(arg)
					}
				}
			}
			return true
		})
	}
	pv.letOutNodes = found
	return found
}

// groupRoots returns the values on entry of the variables of the groups of
// the package that refer to memory. The rules of a group (checkVarGroups)
// make that memory reached only through its variable: its initialiser or
// an assignment made it, every use reads it, writes through its path, or
// hands it to a callee that neither keeps nor returns it, so nothing could
// have converted it into a writer or stored it where a writer reaches. So
// it lies outside every footprint row, as what the parameters reach does
// by the function's own assumption.
func (v *fnVerifier) groupRoots(st *state) []passedValue {
	var roots []passedValue
	// Only a function that names a variable of a group can read what it
	// refers to: no callee hands it back.
	for _, g := range v.groupsNamed(v.fn) {
		for _, variable := range g.vars {
			t := variable.Type()
			if !holdsMemory(t) {
				continue
			}
			var val value
			if v.isAssigned(variable) {
				v.noteGlobal(st, variable)
				val = v.fetch(nil, memory{}, v.globalCells(variable), globalRef(variable), logic.IntLit(0))
			} else {
				saved := v.groupReading
				v.groupReading = true
				fixed, why := v.fixedValue(st, variable)
				v.groupReading = saved
				if why != "" {
					continue
				}
				val = fixed
			}
			roots = append(roots, passedValue{val: val, t: t})
		}
	}
	return roots
}
