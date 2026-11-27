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
		pv.report(c.pos, rAnnotationFault, "%s annotations do not belong on a variable; a var declaration can only have Invariant annotations", c.kind)
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
		pv.report(c.pos, rAnnotationFault, "syntax error in Invariant annotation: %v", err)
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
			pv.report(g.clauses[0].pos, rAnnotationFault, "the invariant of %s cannot be relied on: %s", pv.groupName(g), g.refused)
		}
		for _, variable := range g.vars {
			switch {
			case variable.Exported():
				refuse("%s is exported, and code of another package may assign it; an invariant holds only of variables that only the package changes", variable.Name())
			case pv.isBoxedGlobal(variable) && pv.closedWhy(variable) != "":
				refuse("%s is a struct variable whose address is taken, and %s; one can be in a group only when its address is handed only to trusted functions "+
					"that neither keep it nor run code that could be handed it", variable.Name(), pv.closedWhy(variable))
			case pv.isBoxedGlobal(variable) && pv.addressRuns[variable] != "":
				refuse("%s is a struct variable whose address is taken, and %s, which could see the invariant broken", variable.Name(), pv.addressRuns[variable])
			case pv.isBoxedGlobal(variable):
				// Its address is closed: nothing else reaches it (K2).
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
				if len(init.Lhs) == 1 && init.Lhs[0] == variable && !pv.madeHere(init.Rhs) {
					refuse("the initialiser of %s does not make what it refers to, so something else may hold it", variable.Name())
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
			if pathWritten(pv.info, stack) && !pv.pathStoreFresh(stack) {
				found = fmt.Sprintf("the store through %s at %s puts there a reference to memory that it did not make where it stands, which something else may hold", variable.Name(), pv.placeOfPos(id.Pos()))
				return true
			}
			if use.change == "is assigned" && !pv.assignedFresh(stack) && !pathWritten(pv.info, stack) {
				found = fmt.Sprintf("the assignment to %s at %s puts there a reference to memory that it did not make where it stands, which something else may hold", variable.Name(), pv.placeOfPos(id.Pos()))
				return true
			}
			if !use.escape || use.change == "is assigned" || pathWritten(pv.info, stack) || pv.handedToReader(stack) {
				return true
			}
			// The closed address of a struct variable is handed only to a
			// trusted function that keeps nothing of it and returns nothing
			// that holds memory; the writer that hands it covers the
			// variable and restores the invariant.
			if kindOfChange(use.change) == changeAddress && pv.isBoxedGlobal(variable) && pv.closedWhy(variable) == "" {
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
		if lhs == stack[len(stack)-1] {
			return pv.madeHere(assign.Rhs[i])
		}
	}
	return false
}

// madeHere reports whether an expression makes the memory it refers to
// where it stands, or refers to none: a composite literal, its address,
// make, new, or nil.
func (pv *pkgVerifier) madeHere(e ast.Expr) bool {
	// A value that refers to no memory is made wherever it is.
	if t := pv.info.TypeOf(e); t != nil && !holdsMemory(t) {
		return true
	}
	switch rhs := ast.Unparen(e).(type) {
	case *ast.CompositeLit:
		// Everything the literal holds must be made here too, at every
		// depth (F37 of the review of part 2).
		for _, elt := range rhs.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				if _, isMap := pv.info.TypeOf(rhs).Underlying().(*types.Map); isMap && !pv.madeHere(kv.Key) {
					return false
				}
				elt = kv.Value
			}
			if !pv.madeHere(elt) {
				return false
			}
		}
		return true
	case *ast.UnaryExpr:
		lit, ok := ast.Unparen(rhs.X).(*ast.CompositeLit)
		return rhs.Op == token.AND && ok && pv.madeHere(lit)
	case *ast.CallExpr:
		if tv := pv.info.Types[rhs.Fun]; tv.IsType() && len(rhs.Args) == 1 {
			// []byte or []rune of a constant string.
			return pv.info.Types[rhs.Args[0]].Value != nil
		}
		id, ok := ast.Unparen(rhs.Fun).(*ast.Ident)
		builtin, isBuiltin := pv.info.Uses[id].(*types.Builtin)
		return ok && isBuiltin && (builtin.Name() == "make" || builtin.Name() == "new")
	case *ast.Ident:
		return pv.info.Types[rhs].IsNil()
	}
	return false
}

// pathStoreFresh reports, for a use that is the root of a path a statement
// writes, whether what the statement stores there refers to no memory or
// to memory made where it stands (F36 of the review of part 2): a store of
// a reference to memory that something else holds would let a write
// through that reference reach the group's memory.
func (pv *pkgVerifier) pathStoreFresh(stack []ast.Node) bool {
	for i := len(stack) - 2; i >= 0; i-- {
		if r, ok := stack[i].(*ast.RangeStmt); ok {
			for _, target := range []ast.Expr{r.Key, r.Value} {
				if target != nil && slices.Contains(stack, ast.Node(target)) {
					t := pv.info.TypeOf(target)
					return t == nil || !holdsMemory(t)
				}
			}
			continue
		}
		assign, ok := stack[i].(*ast.AssignStmt)
		if !ok {
			continue
		}
		if len(assign.Lhs) != len(assign.Rhs) {
			return false
		}
		for j, lhs := range assign.Lhs {
			if !slices.Contains(stack, ast.Node(lhs)) {
				continue
			}
			if t := pv.info.TypeOf(lhs); t == nil || !holdsMemory(t) {
				return true
			}
			return pv.madeHere(assign.Rhs[j])
		}
		return true
	}
	// An increment, a delete, or a range target stores no reference.
	return true
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
		// What a node may reach of the functions that code outside the
		// package's verified code can enter, which assume and prove a
		// group's lock clauses (F4 of the design review of F32).
		boundary := map[*callNode]map[*varGroup]bool{}
		for _, node := range nodes {
			boundary[node] = map[*varGroup]bool{}
			if pv.nodeIsBoundary(node) {
				for group := range direct[node] {
					boundary[node][group] = true
				}
			}
		}
		pv.touchedAtBoundary = boundary
		closeOver := func(direct map[*callNode]map[*varGroup]bool) {
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
		}
		close := func() { closeOver(direct); closeOver(boundary) }
		close()
		// A node that calls out of the package may run what such a call
		// reaches: what the package let out, and every exported function
		// and method with an exported name (F33), so a static call of it
		// reaches that too, transitively (F10 of the review of the design
		// of F32). One more closure settles it: what is added is already
		// what those nodes reach.
		outward, outwardBoundary := map[*varGroup]bool{}, map[*varGroup]bool{}
		for _, node := range pv.outwardNodes() {
			for group := range direct[node] {
				outward[group] = true
			}
			for group := range boundary[node] {
				outwardBoundary[group] = true
			}
		}
		for _, node := range nodes {
			if node.out {
				for group := range outward {
					direct[node][group] = true
				}
				for group := range outwardBoundary {
					boundary[node][group] = true
				}
			}
		}
		close()
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
func (v *fnVerifier) groupHolds(g *varGroup, sink *state, mem memory, withLock bool) []*logic.Term {
	// Reading the invariant reads the variables; it is not the function's
	// own reading, which the note on lost contents speaks of.
	saved := v.groupReading
	v.groupReading = true
	defer func() { v.groupReading = saved }()
	env := &specEnv{v: v, sink: sink, now: mem, pos: g.clauses[0].pos}
	var terms []*logic.Term
	for _, c := range g.clauses {
		// One term for each clause, of the conjuncts it keeps.
		var kept []*logic.Term
		for _, node := range c.node.Conjuncts() {
			if withLock || !v.lockConjunct(g, node) {
				kept = append(kept, v.formula(c, node, env))
			}
		}
		terms = append(terms, logic.And(kept...))
	}
	return terms
}

// proveGroups proves the invariants of the groups, read in the state's
// memory, where they must hold: before a call that may assume them, and on
// return of a function that may have changed them.
func (v *fnVerifier) proveGroups(st *state, guard []*logic.Term, groups []*varGroup, pos token.Pos, where string, withLock func(*varGroup) bool) {
	for _, g := range groups {
		// A lock clause is proved only where code outside the package's
		// verified code can enter (F4 of the design review of F32).
		if !withLock(g) {
			saved := v.skipConjunct
			v.skipConjunct = func(node *logic.Node) bool { return v.lockConjunct(g, node) }
			defer func() { v.skipConjunct = saved }()
		} else {
			saved := v.skipConjunct
			v.skipConjunct = nil
			defer func() { v.skipConjunct = saved }()
		}
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
func (v *fnVerifier) assumeGroup(st *state, guard []*logic.Term, mem memory, g *varGroup, from string, withLock bool) {
	for _, t := range v.groupHolds(g, st, mem, withLock) {
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
			switch {
			case v.isBoxedGlobal(variable):
				// A struct variable whose address is closed is written only
				// through its own reference (K2).
				ref := boxRef(variable)
				covers = func(t target) bool { return t.ref != nil && t.ref.Op == logic.OpConst && t.ref.Name == ref.Name }
			case v.isAssigned(variable):
				key := v.globalCells(variable)[0].key
				covers = func(t target) bool { return slices.ContainsFunc(t.cells, func(c cell) bool { return c.key == key }) }
			default:
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
				if v.isBoxedGlobal(variable) {
					pointer := v.boxedPointer(st, variable)
					v.put(st, v.cellsOf(variable.Type()), pointer[0], pointer[1], val)
					continue
				}
				v.noteGlobal(st, variable)
				v.put(st, v.globalCells(variable), globalRef(variable), logic.IntLit(0), val)
			}
			v.groupNames = map[*types.Var]bool{}
			holds := v.groupHolds(g, st, st.mem, true)
			// An invariant reads only the variables of its group, and
			// variables that nothing in the build changes: a writer of any
			// other would not know to restore it (F29 of the review of
			// step 1 of part 2).
			for _, variable := range slices.SortedFunc(maps.Keys(v.groupNames), func(a, b *types.Var) int { return int(a.Pos() - b.Pos()) }) {
				_, written := pv.writtenInBuild()[errorKey(variable)]
				if !slices.Contains(g.vars, variable) && (pv.reassigned[variable] || written || pv.isAssigned(variable)) {
					g.refused = fmt.Sprintf("it names %s, which is not a variable of its group and which the build changes; declare %s in the same var declaration", v.spelling(variable), v.spelling(variable))
					pv.report(g.clauses[0].pos, rAnnotationFault, "the invariant of %s cannot be relied on: %s", pv.groupName(g), g.refused)
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
	// A call of an isolated trusted function that is handed no code runs
	// nothing of the package (F11 of the review of the design of F32).
	isolated := fn.trust != nil && fn.obj != nil && v.isolatedCall(call, fn.obj)
	if !isolated && (fn.obj == nil || fn.obj.Pkg() != v.pass.Pkg || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil) {
		reached = append(reached, v.outwardNodes()...)
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
			if v.isBoxedGlobal(variable) {
				// What a struct variable whose address is closed refers to,
				// from its allocation; its own cells K1 keeps out of rows.
				roots = append(roots, passedValue{val: v.boxedPointer(st, variable), t: types.NewPointer(t)})
				continue
			}
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

// readable reports whether a package-level variable of the package is of an
// interface type or of a named function type with a contract, and verified
// code can read it: it is assigned, or fixed with a value a read can use. A
// variable no verified code can read is relied on by none, as _ or one whose
// value is known only after code of the package has run.
func (pv *pkgVerifier) readable(variable *types.Var) bool {
	if variable.Name() == "_" || !pv.valueVariable(variable.Type()) {
		return false
	}
	if pv.isAssigned(variable) {
		return true
	}
	_, why := pv.usableFixed(variable)
	return why == ""
}

// checkValueInitialisers checks the initialiser of each package-level
// variable of the package whose type is an interface type or a named
// function type with a contract, and that verified code can read, as
// verified code that assigns it would be checked: a value made there is
// checked against the contract of its type (madeAs), and a conversion by
// the conversion check (F41 of the review of part 3). The initialiser is
// code the verifier reads, so what it stores is not taken on trust. What
// the check finds is not reported where the variable is declared, since
// nothing may rely on it, but kept, and a read of the variable in verified
// code reports it (F42): readGlobal, usableFixed, and in another package
// initialisersFact.
func (pv *pkgVerifier) checkValueInitialisers() {
	pv.initWhy, pv.inert, pv.initFacts = map[*types.Var]string{}, map[*types.Var]bool{}, map[*types.Var][]*logic.Term{}
	pv.loggerMade, pv.loggerInert, pv.loggerUse = map[*types.Var]bool{}, map[*types.Var]bool{}, map[*types.Var]string{}
	// A package with no function to verify and no contract on a type of
	// its own is code that is not verified, its initialisers included. One
	// with a contract on a type has values of it that verified code of
	// another package calls, so what its initialisers make is checked (S3
	// of F31's coder, built in F32).
	if !slices.ContainsFunc(pv.order, func(fn *funcInfo) bool { return fn.annotated() }) && len(pv.funcTypes) == 0 && len(pv.ifaceMethods) == 0 {
		return
	}
	check := func(variable *types.Var, task func(v *fnVerifier) bool) {
		var captured []string
		saved := pv.capturing
		pv.capturing = &captured
		inert := false
		pv.run(&funcInfo{obj: types.NewFunc(variable.Pos(), pv.pass.Pkg, "the initialiser of "+variable.Name(), types.NewSignatureType(nil, nil, nil, nil, nil, false))}, func(v *fnVerifier) {
			inert = task(v)
		})
		pv.capturing = saved
		if len(captured) == 0 {
			if inert && !pv.isAssigned(variable) {
				pv.inert[variable] = true
			}
			return
		}
		at, msg, _ := strings.Cut(captured[0], "\x00")
		msg = strings.TrimPrefix(msg, "cannot verify the initialiser of "+variable.Name()+": ")
		pv.initWhy[variable] = fmt.Sprintf("its initialiser does not verify, at %s: %s", at, msg)
	}
	for _, init := range pv.info.InitOrder {
		// Every other initialiser is run as code too, so that a call of a
		// verified function whose Requires may not hold is reported (F1),
		// and so that what it shows of a fixed variable is known to its
		// readers (initcalls.go).
		if len(init.Lhs) > 1 || init.Lhs[0] == nil || !pv.readable(init.Lhs[0]) {
			pv.runInitialiser(init)
		}
		// Variables given by one call with several results are given
		// values no expression of their own makes, which nothing here
		// checks.
		if len(init.Lhs) > 1 {
			for _, variable := range init.Lhs {
				if variable != nil && pv.readable(variable) {
					check(variable, func(v *fnVerifier) bool {
						v.unsupported(init.Rhs.Pos(), rGlobalInit, variable.Name()+" is given one result of a call with several, and a variable of an interface type or of a function type with a contract "+
							"must be given a value of its own, which is checked where it is made")
						return false
					})
				}
			}
			continue
		}
		if init.Lhs[0] == nil || !pv.readable(init.Lhs[0]) {
			continue
		}
		variable := init.Lhs[0]
		check(variable, func(v *fnVerifier) bool {
			// A conversion that go/ssa makes and the walk does not list is
			// checked nowhere, as in a function (vcgen); one go/ssa gives
			// no position may be in this initialiser.
			for _, at := range pv.findConversions().inInit {
				if !at.IsValid() || init.Rhs.Pos() <= at && at < init.Rhs.End() {
					v.unsupported(init.Rhs.Pos(), rConvUnplaced, "Go converts a value to an interface type in the initialiser of "+variable.Name()+
						", and which expression it converts could not be told, so the conversion cannot be checked; give the value a variable of its own type first")
					return false
				}
			}
			st := &state{vals: map[*types.Var]value{}, mem: memory{}, brk: logic.Const("brk", logic.Ref), noted: map[string]bool{}}
			v.entryBrk = st.brk
			st.assume(logic.Le(logic.IntLit(1), st.brk))
			v.openUnit(st)
			v.evalAs(init.Rhs, variable.Type(), st, nil)
			v.closeUnit(st)
			// The value is inert when the initialiser converts a value of
			// a concrete type none of whose methods the interface takes
			// writes behind its receiver, and the interface has no states:
			// its footprint is empty when it is made, as at any such
			// conversion (convert), and no call of its methods adds to it
			// or changes a state of it, so it stays so (O1).
			from := v.info.TypeOf(init.Rhs)
			want := variable.Type()
			return isIface(want) && from != nil && !isIface(from) && !v.info.Types[init.Rhs].IsNil() &&
				!v.hasStates(want) && v.writingImplementation(from, want) == nil
		})
	}
	// What importers read of the exported ones.
	fact := &initialisersFact{Why: map[string]string{}, Inert: map[string]bool{}}
	for variable, why := range pv.initWhy {
		if variable.Exported() {
			fact.Why[variable.Name()] = why
		}
	}
	for variable := range pv.inert {
		if variable.Exported() {
			fact.Inert[variable.Name()] = true
		}
	}
	for variable, facts := range pv.initFacts {
		var size int64
		for _, fact := range facts {
			size += fact.Size()
		}
		if variable.Exported() && size <= maxPublishedFacts {
			if fact.Facts == nil {
				fact.Facts = map[string][]*logic.Term{}
			}
			fact.Facts[variable.Name()] = facts
		}
	}
	if len(fact.Why) > 0 || len(fact.Inert) > 0 || len(fact.Facts) > 0 {
		pv.pass.ExportPackageFact(fact)
	}
}

// initialisersFact holds, for each exported variable of a package whose
// initialiser checkValueInitialisers found wanting, why; a read of it in
// another package reports it. Inert holds the exported variables that
// inertFixed is true of.
type initialisersFact struct {
	Why   map[string]string
	Inert map[string]bool
	// Facts holds what the run of the initialiser of each exported fixed
	// variable shows of its value (initcalls.go), over constants whose
	// names are the same in every package.
	Facts map[string][]*logic.Term
}

func (*initialisersFact) AFact() {}

func (f *initialisersFact) String() string { return fmt.Sprintf("initialisers(%d)", len(f.Why)) }

// initialiserWhy returns why a read of a variable cannot rely on the value
// its initialiser gave it, or "" when it can: the initialiser was checked
// and holds, or the variable is not one whose initialiser is checked.
func (pv *pkgVerifier) initialiserWhy(variable *types.Var) string {
	pkg := variable.Pkg()
	if pkg == nil || variable.Parent() != pkg.Scope() {
		return ""
	}
	if pkg == pv.pass.Pkg {
		return pv.initWhy[variable]
	}
	if pv.initOf == nil {
		pv.initOf = map[*types.Package]*initialisersFact{}
	}
	fact, done := pv.initOf[pkg]
	if !done {
		fact = new(initialisersFact)
		if !pv.pass.ImportPackageFact(pkg, fact) {
			fact = nil
		}
		pv.initOf[pkg] = fact
	}
	if fact == nil {
		return ""
	}
	return fact.Why[variable.Name()]
}

// inertFixed reports whether a fixed variable of an interface type holds a
// value whose footprint is empty and stays so, and that has no states, as
// checkValueInitialisers found of its initialiser.
func (pv *pkgVerifier) inertFixed(variable *types.Var) bool {
	pkg := variable.Pkg()
	if pkg == nil || variable.Parent() != pkg.Scope() {
		return false
	}
	if pkg == pv.pass.Pkg {
		return pv.inert[variable]
	}
	pv.initialiserWhy(variable)
	fact := pv.initOf[pkg]
	return fact != nil && fact.Inert[variable.Name()]
}

// outwardNodes returns what a call out of the package may run of it: what
// the package let out into memory it did not make (F13), and every exported
// function and method with an exported name, of which any package can make
// a value and keep it (F33 of the review of step 2 of part 2), as the call
// graph says of a call through a value.
func (pv *pkgVerifier) outwardNodes() []*callNode {
	found := slices.Clone(pv.letOut())
	for obj, node := range pv.callGraph().byObj {
		if obj.Exported() {
			found = append(found, node)
		}
	}
	return found
}

// Lock clauses (F4 of the design review of F32). A top-level conjunct of a
// group's invariant that reads only states of the group's struct variables
// whose address is closed, as ~held(mu), is assumed on entry of, proved on
// return of, and proved before a call that may reach, only a function that
// code outside the package's verified code can enter: one another package
// can call, init, or one the package lets out. Every other function of the
// package relies on its Requires for the state of the mutex, as a helper
// whose Requires is held(mu) and that runs under the lock. held is about the
// goroutine that runs the function, and only its calls change it; every
// writer of the variable is verified; and a function in between that may
// reach a boundary function under the lock must prove the clause there.

// lockConjunct reports whether a top-level conjunct of a group's invariant
// is a lock clause: S(p) or ~S(p), for a state S of the struct a path p
// that starts at a closed struct variable of the group reaches.
func (pv *pkgVerifier) lockConjunct(g *varGroup, node *logic.Node) bool {
	if node.Kind == logic.NUnary && node.Op == "~" {
		node = node.Kids[0]
	}
	if node.Kind != logic.NCall || len(node.Kids) != 1 {
		return false
	}
	var fields []string
	path := node.Kids[0]
	for path.Kind == logic.NField && !path.Primed {
		fields = append([]string{path.Name}, fields...)
		path = path.Kids[0]
	}
	if path.Kind != logic.NIdent || path.Primed {
		return false
	}
	var root *types.Var
	for _, variable := range g.vars {
		if variable.Name() == path.Name {
			root = variable
		}
	}
	if root == nil || !pv.isBoxedGlobal(root) || pv.closedWhy(root) != "" {
		return false
	}
	t := root.Type()
	for _, name := range fields {
		u, ok := t.Underlying().(*types.Struct)
		if !ok {
			return false
		}
		found := false
		for field := range u.Fields() {
			if field.Name() == name {
				t, found = field.Type(), true
			}
		}
		if !found {
			return false
		}
	}
	u, ok := t.Underlying().(*types.Struct)
	if !ok {
		return false
	}
	return slices.ContainsFunc(statesOf(u), func(decl stateDecl) bool { return decl.name == node.Name })
}

// lockBoundary reports whether code outside the package's verified code
// can enter a function: another package can call it, it is an init
// function, or the package lets it out.
func (pv *pkgVerifier) lockBoundary(fn *funcInfo) bool {
	if fn == nil || fn.obj == nil {
		return true
	}
	if node := pv.callGraph().byObj[pv.originOf(fn.obj)]; node != nil {
		return pv.nodeIsBoundary(node)
	}
	return pv.callableElsewhere(fn.obj)
}

// nodeIsBoundary is lockBoundary for a node of the call graph: a literal
// used as a value is always one.
func (pv *pkgVerifier) nodeIsBoundary(node *callNode) bool {
	if node.fn == nil || node.fn.obj == nil {
		return true
	}
	obj := node.fn.obj
	if pv.callableElsewhere(obj) || obj.Name() == "init" && obj.Type().(*types.Signature).Recv() == nil {
		return true
	}
	return slices.Contains(pv.letOut(), node)
}

// callLockGroups returns the groups whose lock clauses a call may assume:
// those a boundary function it may reach touches, by the call graph, as
// callGroups does for every clause.
func (v *fnVerifier) callLockGroups(call *ast.CallExpr, fn *funcInfo) []*varGroup {
	if len(v.varGroups) == 0 || call == nil {
		return nil
	}
	v.groupsTouched(v.fn)
	var reached []*callNode
	if fn.trust == nil && fn.valueOf == nil && fn.methodOf == nil && fn.obj != nil && fn.obj.Pkg() == v.pass.Pkg {
		if node := v.callGraph().byObj[v.originOf(fn.obj)]; node != nil {
			reached = append(reached, node)
		}
	} else {
		edges := v.callEdges(call, fn)
		if fn.trust != nil {
			edges = v.callGraph().sites[call]
		}
		for _, e := range edges {
			reached = append(reached, e.to)
		}
		isolated := fn.trust != nil && fn.obj != nil && v.isolatedCall(call, fn.obj)
		if !isolated && (fn.obj == nil || fn.obj.Pkg() != v.pass.Pkg || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil) {
			reached = append(reached, v.outwardNodes()...)
		}
	}
	var found []*varGroup
	for _, node := range reached {
		for _, g := range v.varGroups {
			if v.touchedAtBoundary[node][g] && g.refused == "" && !slices.Contains(found, g) {
				found = append(found, g)
			}
		}
	}
	return found
}

// lockContradiction says, for a function whose Requires nothing can
// satisfy, when that comes from a lock clause it assumes because code
// outside the package's verified code can enter it, and its Requires names
// a state of the same variable, as a helper that requires held(mu) and is
// exported (F21 of the review of step 4 of F32); otherwise "".
func (v *fnVerifier) lockContradiction(fn *funcInfo) string {
	if fn.obj == nil || !v.lockBoundary(fn) {
		return ""
	}
	named := map[string]bool{}
	for _, c := range fn.requires {
		if c.node != nil {
			c.node.Walk(func(n *logic.Node) {
				if n.Kind == logic.NIdent {
					named[n.Name] = true
				}
			})
		}
	}
	why := "it is exported"
	switch {
	case fn.obj.Name() == "init":
		why = "it is an init function"
	case fn.obj.Type().(*types.Signature).Recv() != nil && fn.obj.Exported():
		why = "it is a method with an exported name"
	case !fn.obj.Exported():
		why = "it is used as a value or let out of the package"
	}
	for _, g := range v.groupsNamed(fn) {
		for _, c := range g.clauses {
			for _, node := range c.node.Conjuncts() {
				if !v.lockConjunct(g, node) {
					continue
				}
				root := node
				for root.Kind != logic.NIdent && len(root.Kids) > 0 {
					root = root.Kids[0]
				}
				if !named[root.Name] {
					continue
				}
				text := strings.Join(strings.Fields(c.text[node.Start:node.End]), " ")
				return fmt.Sprintf("code outside the package's verified code can call %s (%s), so it assumes %s, a lock clause of the invariant of %s, on entry, "+
					"which its Requires contradicts; keep a function that runs under the lock unexported, and do not use it as a value", fn.obj.Name(), why, text, v.groupName(g))
			}
		}
	}
	return ""
}
