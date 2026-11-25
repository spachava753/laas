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
)

// Assigned package-level variables (part 2 of package-level variables).
//
// A variable of this package that the build changes only by assigning it,
// or a part of it reached through struct fields, is kind 2: its storage
// lies in regions of its own, one for each leaf, keyed varRegion, its key,
// and the leaf's path, at a constant reference that existed on entry (V1
// in the ROADMAP). No pointer refers to that storage, so nothing aliases
// it, and no footprint row holds a cell of it: a write through an interface
// value keeps it (see inEpoch). Reads are recorded reads of memory, so the
// order rule, the versions of a unit, joins, the layers of loops, and the
// havocs of calls work on it as on any memory.

// changeKind says how the build changes a package-level variable.
type changeKind uint8

const (
	changeAssigned changeKind = 1 << iota
	changeAddress
	changeLinked
)

// kindOfChange reads the kind from what findChanges says of a change.
func kindOfChange(what string) changeKind {
	switch {
	case strings.HasPrefix(what, "is assigned"):
		return changeAssigned
	case strings.HasPrefix(what, "has its address taken"):
		return changeAddress
	default:
		return changeLinked
	}
}

// varRegion begins the key of a region that holds a leaf of the storage of
// an assigned package-level variable.
const varRegion = "var "

// isVarRegion reports whether a region holds the storage of an assigned
// package-level variable.
func isVarRegion(key string) bool {
	return strings.HasPrefix(key, varRegion)
}

// assignedWhy reports why a variable of this package that the build
// changes is not an assigned variable that a verified function can read and
// write, or "" when it is one.
func (pv *pkgVerifier) assignedWhy(variable *types.Var) string {
	kinds := pv.changeKinds[variable]
	spelled := pv.spelling(variable)
	t := variable.Type()
	switch {
	case kinds&changeLinked != 0:
		return fmt.Sprintf("%s %s; a variable that a directive or assembly names is another symbol's storage, which code writes under the other name, "+
			"so it cannot be verified", spelled, pv.changeOf[variable])
	case kinds&changeAddress != 0:
		if why := pv.boxedWhy(variable); why != "" {
			return why
		}
		return fmt.Sprintf("%s %s; it is a struct variable whose address is taken, which is read and written as memory, not as an assigned variable", spelled, pv.addressAt(variable))
	case isError(t):
		return fmt.Sprintf("%s %s; package-level error variables that are changed are not supported yet", spelled, pv.ownChanges[variable])
	}
	if _, ok := layoutOf(t); !ok {
		return fmt.Sprintf("%s has type %s, which is not supported%s", spelled, t, unsupportedHint(t))
	}
	if !pv.dataType(t, map[types.Type]bool{}) && !pv.valueVariable(t) {
		return fmt.Sprintf("%s has type %s, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; "+
			"package-level variables of such types that are changed are not supported yet, but for an interface type and a named function type with a contract", spelled, t)
	}
	return ""
}

// valueVariable reports whether a package-level variable of type t holds a
// value whose calls go through contracts (part 3): an interface value, or a
// value of a named function type with a contract. A call through it is a
// call of the contract of its type, as through any value; what it holds was
// made by verified code, checked where it was made, or by code that is not
// verified, assumed to meet the contract.
func (pv *pkgVerifier) valueVariable(t types.Type) bool {
	if isError(t) {
		return false
	}
	if isIface(t) {
		return true
	}
	if _, ok := t.(*types.Named); ok && isFunc(t.Underlying()) {
		return pv.valueContract(t) != nil
	}
	return false
}

// isAssigned reports whether a package-level variable is an assigned
// variable of this package that a verified function can read and write.
func (pv *pkgVerifier) isAssigned(variable *types.Var) bool {
	if variable == nil || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() {
		return false
	}
	if variable.Pkg() == pv.pass.Pkg {
		return pv.reassigned[variable] && pv.assignedWhy(variable) == ""
	}
	fact := pv.publishedFixed(variable)
	if fact == nil || pv.changeKinds[variable]&(changeAddress|changeLinked) != 0 {
		return false
	}
	// A variable that its package leaves alone and that this package
	// assigns is assigned in this build; a proof of its package that relies
	// on its value meets the write (reportSentinelWrites).
	_, fixed := fact.Vars[variable.Name()]
	if !fact.Assigned[variable.Name()] && !(fixed && pv.reassigned[variable] && pv.assignedWhy(variable) == "") {
		return false
	}
	_, taken := pv.writtenInBuild()[errorKey(variable)+addressKey]
	return !taken
}

// addressKey ends the key under which a proof relies on the address of an
// assigned variable never being taken, and under which a package publishes
// a use that takes it (F2 of the design review).
const addressKey = "&"

// globalCells returns the cells of the storage of an assigned variable:
// those of its type, each in a region of its own.
func (pv *pkgVerifier) globalCells(variable *types.Var) []cell {
	cells := slices.Clone(pv.cellsOf(variable.Type()))
	leaves := mustLayout(variable.Type())
	for i := range cells {
		cells[i].key = varRegion + errorKey(variable) + leaves[i].path
	}
	return cells
}

// globalRef is the reference at which the storage of an assigned variable
// lies.
func globalRef(variable *types.Var) *logic.Term {
	return logic.Const("varref "+errorKey(variable), logic.Ref)
}

// noteGlobal states, once on a path, that the storage of an assigned
// variable existed on entry.
func (v *fnVerifier) noteGlobal(st *state, variable *types.Var) {
	if st == nil {
		return
	}
	if v.assignedMet == nil {
		v.assignedMet = map[string]*types.Var{}
	}
	v.assignedMet[errorKey(variable)] = variable
	// A package built later that takes its address or names it in a
	// directive meets this.
	v.reliedKeys[errorKey(variable)+addressKey] = true
	note := "var " + errorKey(variable)
	if st.noted[note] {
		return
	}
	st.noted[note] = true
	ref := globalRef(variable)
	st.assume(logic.And(logic.Not(logic.Eq(ref, logic.RefLit(0))), logic.Lt(ref, v.entryBrk)))
}

// readGlobal reads the value of an assigned variable where it is now.
func (v *fnVerifier) readGlobal(variable *types.Var, pos token.Pos, st *state, guard []*logic.Term) value {
	// A read relies on the value the initialiser gave, unless something
	// assigned it since, which a read cannot tell (F42).
	if why := v.initialiserWhy(variable); why != "" {
		v.unsupported(pos, v.spelling(variable)+" cannot be relied on: "+why)
	}
	v.noteGlobal(st, variable)
	cells, ref := v.globalCells(variable), globalRef(variable)
	return v.readAt(st, guard, v.unit.start(), v.spelling(variable), pos, func(sink *state, mem memory) value {
		val := v.fetch(sink, mem, cells, ref, logic.IntLit(0))
		v.noteTyped(sink, val, variable.Type())
		return val
	})
}

// variableTarget locates a Modifies entry whose path starts at a
// package-level variable. For an assigned variable of this package the path
// starts in its storage; the entry that names the variable alone covers
// that storage and what an entry of a parameter of its type covers, as
// also. For a fixed variable, whose value is a constant, it covers what the
// variable refers to.
func (v *fnVerifier) variableTarget(fn *funcInfo, m *modTarget, variable *types.Var, args map[*types.Var]value, sink *state, mem memory) (shape, target, error) {
	spelled := v.spelling(variable)
	if (fn.spelling().valueOf != nil || fn.spelling().methodOf != nil) && !v.isAssigned(variable) {
		return shape{}, target{}, fmt.Errorf("%s is a package-level variable that is not assigned, which a Modifies clause of a type cannot name", spelled)
	}
	// A contract names a variable of another package only when it is
	// exported; the state of that package covers the others (D1).
	if home := fn.spelling().obj.Pkg(); home != nil && variable.Pkg() != home && v.isBoxedGlobal(variable) {
		return shape{}, target{}, fmt.Errorf("%s is a struct variable of package %s whose address is taken, which a contract of another package cannot name yet; "+
			"list the state of package %s, as // @Modifies %s", spelled, variable.Pkg().Path(), variable.Pkg().Path(), variable.Pkg().Name())
	}
	if home := fn.spelling().obj.Pkg(); home != nil && variable.Pkg() != home && !variable.Exported() && fn.spelling().trust == nil {
		return shape{}, target{}, fmt.Errorf("%s is not exported; list the state of package %s, as // @Modifies %s", spelled, variable.Pkg().Path(), variable.Pkg().Name())
	}
	if _, rest := v.modifiesPath(fn, m); len(rest) != len(m.steps) {
		trimmed := *m
		trimmed.steps = rest
		m = &trimmed
	}
	return v.variableTargetAny(fn, m, variable, args, sink, mem)
}

// variableTargetAny is variableTarget for a variable of any package, as the
// state of a package covers them.
func (v *fnVerifier) variableTargetAny(fn *funcInfo, m *modTarget, variable *types.Var, args map[*types.Var]value, sink *state, mem memory) (shape, target, error) {
	spelled := v.spelling(variable)
	symbolic := mem == nil
	t := variable.Type()
	if v.isBoxedGlobal(variable) {
		return v.boxedTarget(fn, m, variable, args, sink, mem)
	}
	if !v.isAssigned(variable) {
		if v.reassigned[variable] || variable.Pkg() == v.pass.Pkg && v.changeKinds[variable] != 0 {
			return shape{}, target{}, errors.New(v.assignedWhy(variable))
		}
		// An interface value has a footprint and states, which the entry
		// covers, as for an assigned variable (O1 of the orchestrator).
		if !holdsMemory(t) && !isIface(t) || isError(t) {
			return shape{}, target{}, fmt.Errorf("%s is a package-level variable that nothing changes, and what it holds refers to no memory, so there is nothing to modify", spelled)
		}
		if _, why := v.usableFixed(variable); why != "" {
			return shape{}, target{}, errors.New(why)
		}
		root := located{typ: t}
		if !symbolic {
			val, why := v.fixedValue(sink, variable)
			if why != "" {
				return shape{}, target{}, errors.New(why)
			}
			root.val = val
		}
		return v.walkTarget(fn, m, nil, root, t, symbolic, args, sink, mem)
	}
	cells, ref := v.globalCells(variable), globalRef(variable)
	root := located{typ: t, ref: ref, at: logic.IntLit(0), cells: cells}
	if !symbolic {
		v.noteGlobal(sink, variable)
		root.val = v.fetch(sink, mem, cells, ref, root.at)
		v.noteTyped(sink, root.val, t)
	}
	if len(m.steps) > 0 {
		return v.walkTarget(fn, m, nil, root, t, symbolic, args, sink, mem)
	}
	// The storage itself.
	lo, hi := bounds(cells)
	form := shape{cells: cells, lo: lo, hi: hi}
	whole := target{text: m.text, clause: m.clause, cells: cells, single: true}
	if !symbolic {
		whole.ref, whole.lo, whole.hi = ref, logic.IntLit(lo), logic.IntLit(hi)
	}
	// And what its value refers to, as for a parameter of its type.
	if (holdsMemory(t) || isIface(t)) && !isStructType(t) {
		contents := located{typ: t, val: root.val}
		cform, ct, err := v.walkTarget(fn, m, nil, contents, t, symbolic, nil, sink, mem)
		if err != nil {
			return shape{}, target{}, err
		}
		if ct.fp {
			ct.fromVar = variable
		}
		form.also, whole.also = []shape{cform}, []target{ct}
	}
	return form, whole, nil
}

// locateAssigned follows a path of an annotation that starts at an
// assigned variable: in a contract its value when the function is called,
// primed its value on return, and inside a body its current value, or with
// old its value when the function was entered.
func (e *specEnv) locateAssigned(variable *types.Var, steps []logic.Step, when logic.When) (reached, error) {
	spelled := e.v.spelling(variable)
	hops, final, err := plan(variable.Type(), steps, e.writtenIn())
	if err != nil {
		return reached{}, fmt.Errorf("%s%v", spelled, err)
	}
	mem := e.now
	switch when {
	case logic.Old:
		if e.fn != nil {
			return reached{}, fmt.Errorf("old(%s) is only allowed inside a body; in a contract %s already denotes the value on entry", spelled, spelled)
		}
		mem = memory{}
	case logic.Primed:
		switch {
		case e.fn == nil:
			return reached{}, fmt.Errorf("%s' is only allowed in Ensures; inside a body %s already denotes the current value", spelled, spelled)
		case e.post == nil:
			return reached{}, fmt.Errorf("%s' describes the state on return and is only allowed in Ensures", spelled)
		}
		mem = e.post
	}
	e.v.noteGlobal(e.sink, variable)
	val := e.v.fetch(e.sink, mem, e.v.globalCells(variable), globalRef(variable), logic.IntLit(0))
	e.v.noteTyped(e.sink, val, variable.Type())
	cur, ground := e.v.follow(e.sink, mem, val, hops)
	found := reached{val: cur, typ: final, mem: mem, hops: len(hops)}
	if ground {
		found.sink = e.sink
	}
	return found, nil
}

// callableElsewhere reports whether code of another package can call a
// function of this package: it is exported, a method with an exported
// name, or named anywhere in the package other than as the function of a
// call, so that it may be made into a value.
func (pv *pkgVerifier) callableElsewhere(obj types.Object) bool {
	if obj == nil || obj.Exported() {
		return true
	}
	if pv.asValues == nil {
		pv.asValues = map[types.Object]bool{}
		for _, file := range pv.pass.Files {
			var stack []ast.Node
			ast.Inspect(file, func(n ast.Node) bool {
				if n == nil {
					stack = stack[:len(stack)-1]
					return true
				}
				stack = append(stack, n)
				id, ok := n.(*ast.Ident)
				if !ok {
					return true
				}
				used := pv.info.Uses[id]
				if _, isFunc := used.(*types.Func); !isFunc {
					return true
				}
				var expr ast.Node = id
				i := len(stack) - 2
				if i >= 0 {
					if sel, ok := stack[i].(*ast.SelectorExpr); ok && sel.Sel == id {
						expr, i = sel, i-1
					}
				}
				for i >= 0 {
					if paren, ok := stack[i].(*ast.ParenExpr); ok {
						expr, i = paren, i-1
						continue
					}
					break
				}
				if call, ok := stack[max(i, 0)].(*ast.CallExpr); i >= 0 && ok && call.Fun == expr {
					return true
				}
				pv.asValues[used] = true
				return true
			})
		}
	}
	return pv.asValues[obj]
}

// checkHiddenRequires reports each top-level conjunct of a Requires of a
// function that code of another package can call, when it reads a
// package-level variable that is not exported: no caller there can name the
// condition, establish it, or see it fail (F12 of the design review).
func (v *fnVerifier) checkHiddenRequires(st *state) {
	if v.fn.decl == nil || !v.callableElsewhere(v.fn.obj) {
		return
	}
	for _, c := range v.fn.requires {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			scratch := st.clone()
			env := &specEnv{v: v, sink: scratch, fn: v.fn, args: v.entry, now: memory{}}
			t := v.formula(c, conjunct, env)
			regions := map[string]*types.Var{}
			for _, variable := range v.assignedMet {
				for _, c := range v.globalCells(variable) {
					regions[entryRegion+c.key] = variable
				}
			}
			// A kind-3 variable lies in shared regions, at its reference.
			for _, variable := range v.boxedMet {
				regions[boxRef(variable).Name] = variable
			}
			var hidden *types.Var
			seen := map[*logic.Term]bool{}
			var walk func(t *logic.Term)
			walk = func(t *logic.Term) {
				if seen[t] || hidden != nil {
					return
				}
				seen[t] = true
				if variable := regions[t.Name]; t.Op == logic.OpConst && variable != nil && !variable.Exported() {
					hidden = variable
				}
				for _, arg := range t.Args {
					walk(arg)
				}
			}
			walk(t)
			if hidden == nil {
				continue
			}
			v.report(c.pos, "the Requires clause %s reads %s, a package-level variable that is not exported, and code of another package can call %s, "+
				"where no caller can name the condition or see it fail; test the value in the body instead", conjunct, hidden.Name(), v.fn.obj.Name())
		}
	}
}

// reachedWrites returns the package-level variables of this package that
// code of the package a call may run, other than through the frame of a
// verified callee, may write: what the call graph says a call through a
// value, a call of an interface method, or code handed to a trusted
// function may reach, closed under the calls that code makes (F7 of the
// design review). Each is a target of the call, so the caller forgets it
// and its frame must cover it.
func (v *fnVerifier) reachedWrites(call *ast.CallExpr, fn *funcInfo) ([]*types.Var, []*types.Package) {
	if call == nil || fn.trust == nil && fn.valueOf == nil && fn.methodOf == nil {
		return nil, nil
	}
	seen := map[*callNode]bool{}
	var work []*callNode
	edges := v.callEdges(call, fn)
	if fn.trust != nil {
		// What a trusted function does itself its entry says; what it is
		// handed may run.
		edges = v.callGraph().sites[call]
	}
	for _, e := range edges {
		if !seen[e.to] {
			seen[e.to] = true
			work = append(work, e.to)
		}
	}
	found := map[*types.Var]bool{}
	states := map[*types.Package]bool{}
	// frameOf adds what a contract's frame names: variables of any
	// package, and the states of packages (F20 of the review of step 3).
	frameOf := func(contract *funcInfo) {
		for _, m := range contract.modifies {
			if pkg, named, err := v.modifiesPackage(contract, m); named {
				if err == nil {
					states[pkg] = true
				}
				continue
			}
			if variable := v.modifiesVariableOf(contract, m); variable != nil {
				found[variable] = true
			}
		}
	}
	for len(work) > 0 {
		node := work[len(work)-1]
		work = work[:len(work)-1]
		// A verified function writes what its frame covers, which covers
		// what it calls.
		if node.fn != nil && node.fn.annotated() && node.fn.trust == nil {
			frameOf(node.fn)
			continue
		}
		for _, variable := range v.nodeWrites(node) {
			found[variable] = true
		}
		// A call by name into another package writes what the callee's
		// body, and what it calls by name, writes, as its package
		// publishes it (writesFact).
		for _, callee := range v.nodeCallsOut(node) {
			fact := new(writesFact)
			if !v.pass.ImportObjectFact(callee.Origin(), fact) {
				continue
			}
			// Only a variable that a proof can read matters: one of this
			// package, an exported one, or one of a package with functions
			// that have annotations, whose contracts may speak of it. An
			// unexported variable of a package with none is read by no
			// proof, as what errors.New writes of package runtime.
			readable := func(variable *types.Var) bool {
				if variable.Pkg() == v.pass.Pkg || variable.Exported() {
					return true
				}
				covers := new(coversFact)
				return v.pass.ImportPackageFact(variable.Pkg(), covers) && covers.Verified
			}
			for _, key := range slices.Concat(slices.Sorted(maps.Keys(fact.Keys)), slices.Sorted(maps.Keys(fact.Through))) {
				if variable := v.lookupKey(key); variable != nil && readable(variable) {
					found[variable] = true
				}
			}
		}
		for _, e := range node.edges {
			if !seen[e.to] {
				seen[e.to] = true
				work = append(work, e.to)
			}
		}
	}
	vars := slices.SortedFunc(func(yield func(*types.Var) bool) {
		for variable := range found {
			if !yield(variable) {
				return
			}
		}
	}, func(a, b *types.Var) int {
		if c := strings.Compare(a.Pkg().Path(), b.Pkg().Path()); c != 0 {
			return c
		}
		return int(a.Pos() - b.Pos())
	})
	pkgs := slices.SortedFunc(func(yield func(*types.Package) bool) {
		for pkg := range states {
			if !yield(pkg) {
				return
			}
		}
	}, func(a, b *types.Package) int { return strings.Compare(a.Path(), b.Path()) })
	return vars, pkgs
}

// nodeCallsOut returns the functions of other packages that the body of a
// node of the call graph calls by name.
func (v *fnVerifier) nodeCallsOut(node *callNode) []*types.Func {
	var body *ast.BlockStmt
	switch {
	case node.lit != nil:
		body = node.lit.Body
	case node.fn != nil && node.fn.decl != nil:
		body = node.fn.decl.Body
	}
	var out []*types.Func
	if body == nil {
		return nil
	}
	ast.Inspect(body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		if callee := v.calleeAt(call); callee != nil && callee.Pkg() != nil && callee.Pkg() != v.pass.Pkg && !slices.Contains(out, callee) {
			out = append(out, callee)
		}
		return true
	})
	return out
}

// nodeWrites returns the package-level variables of this package that the
// body of a node of the call graph changes, or may write what it refers to
// through: every use that changes one, or that lets a reference to what one
// that refers to memory holds out of it, which may be a write.
func (v *fnVerifier) nodeWrites(node *callNode) []*types.Var {
	if v.writesOf == nil {
		v.writesOf = map[*callNode][]*types.Var{}
	}
	if found, done := v.writesOf[node]; done {
		return found
	}
	var body *ast.BlockStmt
	switch {
	case node.lit != nil:
		body = node.lit.Body
	case node.fn != nil && node.fn.decl != nil:
		body = node.fn.decl.Body
	}
	var found []*types.Var
	if body != nil {
		var stack []ast.Node
		ast.Inspect(body, func(n ast.Node) bool {
			if n == nil {
				stack = stack[:len(stack)-1]
				return true
			}
			stack = append(stack, n)
			id, ok := n.(*ast.Ident)
			if !ok {
				return true
			}
			variable, ok := v.info.Uses[id].(*types.Var)
			if !ok || variable.Pkg() != v.pass.Pkg || variable.Parent() != v.pass.Pkg.Scope() || slices.Contains(found, variable) {
				return true
			}
			if use := v.useOf(stack); use.change != "" || use.escape && holdsMemory(variable.Type()) {
				found = append(found, variable)
			}
			return true
		})
	}
	v.writesOf[node] = found
	return found
}

// reachedTargets returns the targets of what reachedWrites finds, read in
// mem, and their shapes.
func (v *fnVerifier) reachedTargets(call *ast.CallExpr, fn *funcInfo, sink *state, mem memory) ([]shape, []target) {
	var forms []shape
	var targets []target
	add := func(form shape, t target) {
		forms = append(forms, append([]shape{form}, form.also...)...)
		for _, each := range append([]target{t}, t.also...) {
			each.also, each.mod, each.reached, each.fromVar = nil, -1, true, nil
			targets = append(targets, splitStates(each)...)
			for _, part := range each.owned {
				part.mod, part.text, part.part, part.reached = -1, each.text, true, true
				targets = append(targets, part)
			}
		}
	}
	vars, pkgs := v.reachedWrites(call, fn)
	for _, variable := range vars {
		kept := v.isAssigned(variable) || v.isBoxedGlobal(variable)
		if !kept && (v.reassigned[variable] || !holdsMemory(variable.Type()) || isError(variable.Type())) {
			continue
		}
		if _, why := v.usableFixed(variable); !kept && why != "" {
			continue
		}
		m := &modTarget{name: variable.Name(), text: v.spelling(variable)}
		form, t, err := v.variableTargetAny(v.fn, m, variable, nil, sink, mem)
		if err != nil {
			// What the call may write cannot be named, so it cannot be
			// forgotten: the call is not followed (F20).
			v.unsupported(call.Pos(), fmt.Sprintf("code that the call may run writes %s, which cannot be followed: %v", v.spelling(variable), err))
		}
		add(form, t)
	}
	for _, pkg := range pkgs {
		if pkg == v.pass.Pkg {
			continue
		}
		m := &modTarget{text: pkg.Name(), pkgPath: pkg.Path()}
		form, t, err := v.stateTarget(v.fn, m, pkg, sink, mem)
		if err != nil {
			v.unsupported(call.Pos(), fmt.Sprintf("code that the call may run changes the state of package %s, which cannot be followed: %v", pkg.Path(), err))
		}
		// A state with no variable that verified code can write changes
		// nothing a proof reads.
		if len(t.cells) == 0 && t.mapType == nil && len(t.also) == 0 {
			continue
		}
		add(form, t)
	}
	return forms, targets
}
