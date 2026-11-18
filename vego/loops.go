package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"go/version"
	"maps"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/types/typeutil"
)

// site is a place in a loop that may write memory: positions of an
// allocation in some regions, or a map.
type site struct {
	cells []cell
	// elem is set when the site may write any element of a slice, and
	// mapType when it may write a map.
	elem    types.Type
	mapType types.Type
	// root is the variable that holds the pointer, the slice, or the map,
	// when the site is that simple. A site without one may write any
	// allocation its regions have. For a pointer, lo and hi bound the
	// positions written from where the pointer points.
	root   *types.Var
	lo, hi int64
}

// effects describes what a loop may change.
type effects struct {
	// whole holds the variables the loop assigns, and grown those among
	// them whose every assignment has the form x = append(x, ...).
	whole map[*types.Var]bool
	grown map[*types.Var]bool
	sites []site
}

// localVar returns the local variable an expression names, if it is one.
func (v *fnVerifier) localVar(e ast.Expr) *types.Var {
	if e == nil {
		return nil
	}
	id, ok := ast.Unparen(e).(*ast.Ident)
	if !ok {
		return nil
	}
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	return variable
}

// holder returns the variable that holds the pointer, slice, or map an
// argument passes for a parameter of the given type, if there is one: the
// argument is the variable, or the address of a variable that lives in
// memory, written out or taken by a method call.
func (v *fnVerifier) holder(arg ast.Expr, want types.Type) *types.Var {
	arg = ast.Unparen(arg)
	t := v.info.TypeOf(arg)
	if address, ok := arg.(*ast.UnaryExpr); ok && address.Op == token.AND {
		arg, t = ast.Unparen(address.X), types.NewPointer(v.info.TypeOf(address.X))
	} else if variable := v.localVar(arg); variable != nil && v.boxed[variable] {
		t = types.NewPointer(t)
	} else if variable != nil && types.Identical(t, want) {
		return variable
	} else {
		return nil
	}
	if variable := v.localVar(arg); variable != nil && v.boxed[variable] && types.Identical(t, want) {
		return variable
	}
	return nil
}

// effects computes what a loop may change: the variables it assigns and the
// memory it may write, directly or through a call.
func (v *fnVerifier) effects(nodes ...ast.Node) *effects {
	eff := &effects{whole: map[*types.Var]bool{}, grown: map[*types.Var]bool{}}
	otherwise := map[*types.Var]bool{}
	assigned := func(e ast.Expr, appendedTo *types.Var) {
		if e == nil {
			return
		}
		lv := v.place(e)
		switch {
		case lv.box != nil:
			// Creating the variable writes nothing that existed before.
			if id, ok := ast.Unparen(e).(*ast.Ident); ok && v.info.Defs[id] != nil {
				break
			}
			lo, hi := bounds(lv.cells)
			eff.sites = append(eff.sites, site{cells: lv.cells, root: lv.box, lo: lo, hi: hi})
		case lv.kind == placeLocal:
			eff.whole[lv.local] = true
			if appendedTo != lv.local || len(lv.leaves) != len(mustLayout(lv.local.Type())) {
				otherwise[lv.local] = true
			}
		case lv.kind == placeMem && lv.pointer != nil:
			lo, hi := bounds(lv.cells)
			eff.sites = append(eff.sites, site{cells: lv.cells, root: v.localVar(lv.pointer), lo: lo, hi: hi})
		case lv.kind == placeMem:
			eff.sites = append(eff.sites, site{cells: lv.cells, elem: elemType(v.info.TypeOf(lv.slice)), root: v.localVar(lv.slice)})
		case lv.kind == placeMap:
			eff.sites = append(eff.sites, site{mapType: lv.mapType, root: v.localVar(lv.slice)})
		}
	}
	visit := func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.AssignStmt:
			var appendedTo *types.Var
			if len(n.Lhs) == 1 && len(n.Rhs) == 1 && v.isAppend(n.Rhs[0]) {
				call := ast.Unparen(n.Rhs[0]).(*ast.CallExpr)
				appendedTo = v.localVar(call.Args[0])
				// Appending may write into the capacity of the slice.
				if t := v.info.TypeOf(call.Args[0]); isSlice(t) {
					eff.sites = append(eff.sites, site{cells: v.cellsOf(elemType(t)), elem: elemType(t), root: appendedTo})
				}
			}
			for _, lhs := range n.Lhs {
				assigned(lhs, appendedTo)
			}
		case *ast.IncDecStmt:
			assigned(n.X, nil)
		case *ast.RangeStmt:
			assigned(n.Key, nil)
			assigned(n.Value, nil)
		case *ast.CallExpr:
			if isBuiltin(v.info, n, "delete") && isMap(v.info.TypeOf(n.Args[0])) {
				eff.sites = append(eff.sites, site{mapType: v.info.TypeOf(n.Args[0]), root: v.localVar(n.Args[0])})
			}
			v.callSites(n, eff)
		}
		return true
	}
	for _, node := range nodes {
		if node != nil {
			ast.Inspect(node, visit)
		}
	}
	for variable := range eff.whole {
		eff.grown[variable] = !otherwise[variable]
	}
	return eff
}

// callSites adds what a call inside a loop may write, according to the
// Modifies clauses of the function called.
func (v *fnVerifier) callSites(call *ast.CallExpr, eff *effects) {
	callee, _ := typeutil.Callee(v.info, call).(*types.Func)
	if callee == nil || errorConstructor(callee) {
		return
	}
	fn := v.contractOf(callee)
	if fn == nil {
		return
	}
	sig := callee.Type().(*types.Signature)
	argument := func(param *types.Var) ast.Expr {
		if param == sig.Recv() {
			sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
			if selection := v.info.Selections[sel]; ok && selection != nil && len(selection.Index()) == 1 {
				return sel.X
			}
			return nil
		}
		for i := range min(sig.Params().Len(), len(call.Args)) {
			if sig.Params().At(i) == param {
				return call.Args[i]
			}
		}
		return nil
	}
	for _, m := range fn.modifies {
		form, _, err := v.locateTarget(fn, m, nil, nil, nil)
		if err != nil {
			v.misread(m.clause, err)
		}
		at := site{cells: form.cells, elem: form.elem, mapType: form.mapType, lo: form.lo, hi: form.hi}
		// Only a pointer or slice passed as it is names the same object
		// before and inside the call.
		if arg := argument(form.param); form.direct && arg != nil {
			at.root = v.holder(arg, form.param.Type())
		}
		eff.sites = append(eff.sites, at)
	}
}

// freshEachIteration reports whether the loop at a position gives each
// iteration variables of its own, as Go does from version 1.22 on. The
// version is that of the file, set by go.mod or a build constraint; a file
// without one is compiled as the newest Go.
func (pv *pkgVerifier) freshEachIteration(pos token.Pos) bool {
	for _, file := range pv.pass.Files {
		if file.FileStart <= pos && pos < file.FileEnd {
			language := pv.info.FileVersions[file]
			return language == "" || version.Compare(language, "go1.22") >= 0
		}
	}
	return true
}

// forget gives fresh values to everything a loop may change, which then
// stand for the state at the start of an arbitrary iteration. st is the
// state before the loop, which the result is a copy of.
//
// A variable the loop assigns becomes unknown. A region of memory the loop
// writes becomes unknown too, but two things remain known about it. If every
// write to the region goes through a variable the loop does not assign, or
// through a slice the loop only appends to, then every other object that
// existed before the loop is unchanged. Otherwise only this is known:
// whatever existed when the function was entered and is not listed in a
// Modifies clause is unchanged, since no write may touch it.
func (v *fnVerifier) forget(st *state, eff *effects) *state {
	head := st.clone()
	v.forgotten = map[string]forgottenPart{}
	head.brk = v.fresh("brk", logic.Ref)
	head.assume(logic.Le(st.brk, head.brk))
	var variables []*types.Var
	for variable := range head.vals {
		if eff.whole[variable] {
			variables = append(variables, variable)
		}
	}
	slices.SortFunc(variables, func(a, b *types.Var) int { return int(a.Pos() - b.Pos()) })
	for _, variable := range variables {
		before := st.vals[variable]
		if v.boxed[variable] {
			// A variable of the loop that lives in memory is a new one in
			// each iteration: the one the loop started with, or one made
			// since.
			ref := v.fresh(variable.Name(), logic.Ref)
			head.vals[variable] = value{ref, logic.IntLit(0)}
			made := logic.And(logic.Lt(logic.IntLit(0), ref), logic.Lt(ref, head.brk))
			if v.pass.TypesSizes.Sizeof(variable.Type()) > 0 {
				made = logic.And(logic.Le(st.brk, ref), logic.Lt(ref, head.brk))
			}
			head.assume(logic.Or(logic.Eq(ref, before[0]), made))
			continue
		}
		now := v.unknown(variable.Name(), variable.Type(), head)
		for index, part := range now {
			v.forgotten[part.Name] = forgottenPart{variable: variable, index: index}
		}
		head.vals[variable] = now
		if eff.grown[variable] && isSlice(variable.Type()) {
			// A slice that is only appended to is still in its old array,
			// or in one created since.
			inOld := logic.And(logic.Eq(now[0], before[0]), logic.Eq(now[1], before[1]), logic.Eq(now[3], before[3]), logic.Le(before[2], now[2]))
			inNew := logic.And(logic.Le(st.brk, now[0]), logic.Eq(now[1], logic.IntLit(0)))
			if v.pass.TypesSizes.Sizeof(elemType(variable.Type())) == 0 {
				// An array of elements without size has no identity:
				// it may be where anything else is.
				inNew = logic.Eq(now[1], logic.IntLit(0))
			}
			head.assume(logic.Or(inOld, inNew))
		}
	}
	type writes struct {
		sort    logic.Sort
		precise bool
		flat    bool
		targets []target
	}
	regions := map[string]*writes{}
	for _, at := range eff.sites {
		val := st.vals[at.root]
		precise := at.root != nil && val != nil && (!eff.whole[at.root] || (at.elem != nil && eff.grown[at.root]))
		t := target{cells: at.cells, elem: at.elem, mapType: at.mapType}
		switch {
		case !precise:
		case at.mapType != nil:
			t.ref = val[0]
		case at.elem != nil:
			t.ref, t.lo = val[0], val[1]
			t.hi = logic.Add(val[1], logic.Mul(val[3], logic.IntLit(v.span(at.elem))))
		default:
			t.ref, t.lo, t.hi = val[0], logic.Add(val[1], logic.IntLit(at.lo)), logic.Add(val[1], logic.IntLit(at.hi))
		}
		t.regions(func(key string, sort logic.Sort) {
			if regions[key] == nil {
				// The count of a map is one number for each map; every
				// other region has a sequence for each allocation.
				flat := t.mapType != nil && key == mapOwner(t.mapType)+countLeaf.path
				regions[key] = &writes{sort: sort, precise: true, flat: flat}
			}
			regions[key].precise = regions[key].precise && precise
			regions[key].targets = append(regions[key].targets, t)
		})
	}
	for _, key := range slices.Sorted(maps.Keys(regions)) {
		written := regions[key]
		sort := logic.SeqOf(logic.SeqOf(written.sort))
		if written.flat {
			sort = logic.SeqOf(written.sort)
		}
		known := &layer{prev: st.mem.region(key, sort), bound: st.brk, targets: written.targets, flat: written.flat}
		if !written.precise {
			known.bound, known.targets = v.entryBrk, nil
			for _, t := range v.frame {
				if t.reaches([]string{key}) {
					known.targets = append(known.targets, t)
				}
			}
		}
		forgotten := v.fresh("mem'"+key, sort)
		v.layers[forgotten.Name] = known
		head.mem[key] = forgotten
	}
	return head
}

// loopShape describes a for or range loop to the shared loop rule.
type loopShape struct {
	pos     token.Pos
	body    *ast.BlockStmt
	post    ast.Stmt
	spec    *loopSpec
	effects *effects
	// step yields the counter of the next iteration when it is not simply
	// one more, as when ranging over the characters of a string.
	step   func(st *state, counter *logic.Term) *logic.Term
	cond   func(st *state) *logic.Term // for loops: evaluates the condition
	always bool                        // the loop has no condition and is only left by break
	// Range loops run a fixed number of iterations; bind stores the iteration
	// counter and the current element in the loop variables.
	limit *logic.Term
	bind  func(st *state, counter *logic.Term)
	// renewed holds the variables a for statement declares that live in
	// memory. Each iteration has its own: at the end of an iteration, before
	// the post statement, the next one is created with the value of the
	// current one, and pointers to the current one keep pointing to it.
	renewed []*types.Var
}

// loop verifies a loop by induction. The invariants are checked on entry.
// Then an arbitrary iteration is examined: what the loop may change is
// forgotten, the invariants are assumed, and the body must re-establish the
// invariants and decrease the variant. Code after the loop continues from the
// state in which the condition is false, or from a break.
func (v *fnVerifier) loop(shape loopShape, st *state, k func(*state)) {
	at := shape.body.Lbrace + 1
	spec := shape.spec
	checkInvariants := func(st *state, what string) {
		for _, c := range spec.invariants {
			v.checkClause(c, v.bodyEnv(st, at), st, nil, shape.pos, what)
		}
	}
	var counter *logic.Term
	entry := st.clone()
	if shape.limit != nil {
		shape.bind(entry, logic.IntLit(0))
	}
	checkInvariants(entry, "loop invariant may not hold on entry")

	head := v.forget(st, shape.effects)
	forgotten := v.forgotten
	if shape.limit != nil {
		counter = v.fresh("iteration", logic.Int)
		head.assume(logic.Le(logic.IntLit(0), counter))
		head.assume(logic.Le(counter, shape.limit))
		shape.bind(head, counter)
	}
	for _, c := range spec.invariants {
		head.assume(v.formula(c, c.node, v.bodyEnv(head, at)))
	}
	// What is known of the unknowns at the head: their types, and the
	// invariants, on every path that comes to the loop; see tieFailures.
	summary := &forward{facts: slices.Clip(head.hyps[len(st.hyps):])}
	for _, taken := range st.chosen {
		summary.path = append(summary.path, taken.cond)
	}
	var cond *logic.Term
	if shape.limit != nil {
		cond = logic.Lt(counter, shape.limit)
	} else {
		cond = shape.cond(head)
	}
	if !shape.always {
		exit := head.clone()
		exit.decide(logic.Not(cond))
		k(exit)
	}
	head.decide(cond)
	var before *logic.Term
	if spec.variant != nil {
		before = v.intTerm(spec.variant, v.bodyEnv(head, at))
		v.check(head, nil, logic.Le(logic.IntLit(0), before), shape.pos,
			"loop variant may be negative: %s", spec.variant.text)
	}
	finish := func(end *state) {
		if shape.limit != nil {
			next := logic.Add(counter, logic.IntLit(1))
			if shape.step != nil {
				next = shape.step(end, counter)
			}
			shape.bind(end, next)
			// The counter of the loop is forgotten like a variable: how
			// far the loop has come depends on whatever let the iterations
			// before this one run to their end.
			v.left = append(v.left, leftover{name: counter.Name, val: next, facts: slices.Clip(end.hyps), loop: summary,
				path: slices.Clip(end.chosen[len(summary.path):])})
		}
		// A variable the loop forgot stands, at the head, for what an
		// earlier iteration left in it, which is recorded here; see
		// tieFailures.
		for name, lost := range forgotten {
			if held := end.vals[lost.variable]; held != nil {
				v.left = append(v.left, leftover{name: name, val: held[lost.index], facts: slices.Clip(end.hyps), loop: summary,
					path: slices.Clip(end.chosen[len(summary.path):])})
			}
		}
		checkInvariants(end, "loop invariant may not be preserved")
		if before != nil {
			v.check(end, nil, logic.Lt(v.intTerm(spec.variant, v.bodyEnv(end, at)), before), shape.pos,
				"loop variant may not decrease: %s", spec.variant.text)
		}
	}
	after := func(end *state) {
		for _, variable := range shape.renewed {
			v.bind(end, variable, v.current(end, variable))
		}
		if shape.post != nil {
			// The post statement may continue in more than one state.
			v.stmt(shape.post, end, ctrl{}, finish)
			return
		}
		finish(end)
	}
	v.seq(shape.body.List, shape.body.Lbrace, shape.body.Rbrace, head, ctrl{brk: k, cont: after}, after)
}

// forStmt verifies a for statement. renewed lists the variables its
// initializer declared that live in memory, once the initializer has run.
func (v *fnVerifier) forStmt(s *ast.ForStmt, spec *loopSpec, renewed []*types.Var, st *state, k func(*state)) {
	if s.Init != nil {
		// Since Go 1.22 each iteration has variables of its own. Before
		// that the loop had one set, which needs nothing special.
		if init, ok := s.Init.(*ast.AssignStmt); ok && init.Tok == token.DEFINE && v.freshEachIteration(s.Pos()) {
			for _, lhs := range init.Lhs {
				id, _ := lhs.(*ast.Ident)
				if variable, ok := v.info.Defs[id].(*types.Var); ok && v.boxed[variable] {
					renewed = append(renewed, variable)
				}
			}
		}
		// The initializer may continue in more than one state.
		v.stmt(s.Init, st, ctrl{}, func(next *state) {
			without := *s
			without.Init = nil
			v.forStmt(&without, spec, renewed, next, k)
		})
		return
	}
	if spec.variant == nil {
		v.report(s.Pos(), "loop needs a // @Variant annotation to prove that it terminates")
	}
	shape := loopShape{pos: s.Pos(), body: s.Body, post: s.Post, spec: spec, always: s.Cond == nil, renewed: renewed}
	shape.effects = v.effects(s.Body, s.Post)
	for _, variable := range renewed {
		shape.effects.whole[variable] = true
	}
	shape.cond = func(st *state) *logic.Term {
		if s.Cond == nil {
			return logic.True()
		}
		return v.expr(s.Cond, st, nil)
	}
	v.loop(shape, st, k)
}

// rangeStmt verifies "for i := range n" and "for i, x := range A" as counted
// loops. The iteration count is fixed on entry, so termination needs no
// variant, and the facts 0 <= i <= limit are part of the invariant for free.
// As in Go, the slice is evaluated once, and each iteration reads the
// element as it is at that moment.
func (v *fnVerifier) rangeStmt(s *ast.RangeStmt, spec *loopSpec, st *state, k func(*state)) {
	shape := loopShape{pos: s.Pos(), body: s.Body, spec: spec}
	shape.effects = v.effects(s.Body)
	if s.Tok == token.ASSIGN {
		v.unsupported(s.Pos(), "range loops must declare their variables with :=")
	}
	variable := func(e ast.Expr) *types.Var {
		if id, ok := e.(*ast.Ident); ok && id.Name != "_" {
			return v.info.Defs[id].(*types.Var)
		}
		return nil
	}
	key, element := variable(s.Key), variable(s.Value)
	if (v.boxed[key] || v.boxed[element]) && !v.freshEachIteration(s.Pos()) {
		v.unsupported(s.Pos(), "before Go 1.22 the iterations of a range loop share their variables, "+
			"which is not supported when the address of one is taken")
	}
	ranged := v.info.TypeOf(s.X)
	sort, single := sortOf(ranged)
	switch {
	case single && sort == logic.Int:
		count := v.expr(s.X, st, nil)
		shape.limit = logic.Ite(logic.Le(logic.IntLit(0), count), count, logic.IntLit(0))
		shape.bind = func(st *state, counter *logic.Term) {
			if key != nil {
				v.bind(st, key, value{counter})
			}
		}
	case isString(ranged):
		// Ranging over a string decodes UTF-8: each iteration yields some
		// character and moves on by the one to four bytes it occupies,
		// never past the end. Which character, and how many bytes, is not
		// modelled.
		shape.limit = logic.Len(v.expr(s.X, st, nil))
		shape.step = func(st *state, counter *logic.Term) *logic.Term {
			next := v.fresh("offset", logic.Int)
			st.assume(logic.And(logic.Lt(counter, next), logic.Le(next, logic.Add(counter, logic.IntLit(4))), logic.Le(next, shape.limit)))
			return next
		}
		shape.bind = func(st *state, counter *logic.Term) {
			if key != nil {
				v.bind(st, key, value{counter})
			}
			if element != nil {
				v.bind(st, element, v.unknown("char", element.Type(), st))
			}
		}
	case isMap(ranged) && mapModelled(ranged):
		// A map is visited once for each key it has, in an order nobody
		// knows. Each iteration gets some key the map has; that the keys of
		// different iterations differ is not modelled. A loop that changes
		// a map of the type while ranging over one is not supported.
		for _, at := range shape.effects.sites {
			if at.mapType != nil && mapOwner(at.mapType) == mapOwner(ranged) {
				v.unsupported(s.Pos(), "the loop modifies a map of the type it ranges over, which is not supported")
			}
		}
		ref := v.expr(s.X, st, nil)
		shape.limit = v.mapLen(st, st.mem, ranged, ref)
		keyType, _ := mapParts(ranged)
		shape.bind = func(st *state, counter *logic.Term) {
			at := v.unknown("key", keyType, st)[0]
			st.assume(logic.Implies(logic.Lt(counter, shape.limit), v.mapHas(st, st.mem, ranged, ref, at)))
			if key != nil {
				v.bind(st, key, value{at})
			}
			if element != nil {
				v.bind(st, element, v.mapValue(st, st.mem, ranged, ref, at))
			}
		}
	case isSlice(ranged):
		header := v.eval(s.X, st, nil)
		shape.limit = header[2]
		shape.bind = func(st *state, counter *logic.Term) {
			if key != nil {
				v.bind(st, key, value{counter})
			}
			if element == nil {
				return
			}
			current, ok := v.element(st, st.mem, header, ranged, counter)
			if !ok {
				v.unsupported(s.X.Pos(), fmt.Sprintf("slices of %s are not supported", elemType(ranged)))
			}
			v.bind(st, element, current)
		}
	default:
		v.unsupported(s.X.Pos(), fmt.Sprintf("range over %s is not supported", ranged))
	}
	v.loop(shape, st, k)
}
