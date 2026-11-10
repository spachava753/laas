package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/types/typeutil"
)

// site is a place in a loop that may write memory: fields of an object, or
// elements of a backing array.
type site struct {
	typ    types.Type
	elems  bool
	prefix string
	// root is the variable that holds the pointer to the object, or the
	// slice of the array, when the site is that simple. A site without one
	// may write any object or array of its type.
	root *types.Var
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
		switch lv.kind {
		case placeLocal:
			eff.whole[lv.local] = true
			if appendedTo != lv.local || len(lv.prefix) > 0 {
				otherwise[lv.local] = true
			}
		case placeField:
			eff.sites = append(eff.sites, site{typ: lv.owner, prefix: lv.prefix, root: v.localVar(lv.base)})
		case placeElem:
			eff.sites = append(eff.sites, site{typ: lv.owner, elems: true, prefix: lv.prefix, root: v.localVar(lv.base)})
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
					eff.sites = append(eff.sites, site{typ: elemType(t), elems: true, root: appendedTo})
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
		form, err := fn.shapeOf(m, nil)
		if err != nil {
			v.misread(m.clause, err)
		}
		at := site{typ: form.typ, elems: form.elems, prefix: form.prefix}
		// Only a pointer or slice passed as it is names the same object
		// before and inside the call.
		if arg := argument(form.param); form.direct && arg != nil && types.Identical(v.info.TypeOf(arg), form.param.Type()) {
			at.root = v.localVar(arg)
		}
		eff.sites = append(eff.sites, at)
	}
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
		now := v.unknown(variable.Name(), variable.Type(), head)
		head.vals[variable] = now
		if eff.grown[variable] && isSlice(variable.Type()) {
			// A slice that is only appended to is still in its old array,
			// or in one created since.
			inOld := logic.And(logic.Eq(now[0], before[0]), logic.Eq(now[1], before[1]), logic.Eq(now[3], before[3]), logic.Le(before[2], now[2]))
			inNew := logic.And(logic.Le(st.brk, now[0]), logic.Eq(now[1], logic.IntLit(0)))
			head.assume(logic.Or(inOld, inNew))
		}
	}
	type writes struct {
		lf      leaf
		elems   bool
		precise bool
		targets []target
	}
	regions := map[string]*writes{}
	for _, at := range eff.sites {
		val := st.vals[at.root]
		precise := at.root != nil && val != nil && (!eff.whole[at.root] || (at.elems && eff.grown[at.root]))
		t := target{typ: at.typ, elems: at.elems, prefix: at.prefix}
		if precise {
			t.ref = val[0]
			if at.elems {
				t.lo, t.hi = val[1], logic.Add(val[1], val[3])
			}
		}
		t.regions(func(key string, lf leaf) {
			if regions[key] == nil {
				regions[key] = &writes{lf: lf, elems: at.elems, precise: true}
			}
			regions[key].precise = regions[key].precise && precise
			regions[key].targets = append(regions[key].targets, t)
		})
	}
	for _, key := range slices.Sorted(maps.Keys(regions)) {
		written := regions[key]
		sort := logic.SeqOf(written.lf.sort)
		if written.elems {
			sort = logic.SeqOf(sort)
		}
		known := &layer{prev: st.mem.region(key, sort), bound: st.brk, targets: written.targets, elems: written.elems}
		if !written.precise {
			known.bound, known.targets = v.entryBrk, nil
			for _, t := range v.frame {
				if t.elems == written.elems && under(key, t.owner()+t.prefix) {
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
	if shape.limit != nil {
		counter = v.fresh("iteration", logic.Int)
		head.assume(logic.Le(logic.IntLit(0), counter))
		head.assume(logic.Le(counter, shape.limit))
		shape.bind(head, counter)
	}
	for _, c := range spec.invariants {
		head.assume(v.formula(c, c.node, v.bodyEnv(head, at)))
	}
	var cond *logic.Term
	if shape.limit != nil {
		cond = logic.Lt(counter, shape.limit)
	} else {
		cond = shape.cond(head)
	}
	if !shape.always {
		exit := head.clone()
		exit.assume(logic.Not(cond))
		k(exit)
	}
	head.assume(cond)
	var before *logic.Term
	if spec.variant != nil {
		before = v.intTerm(spec.variant, v.bodyEnv(head, at))
		v.check(head, nil, logic.Le(logic.IntLit(0), before), shape.pos,
			"loop variant may be negative: %s", spec.variant.text)
	}
	var after func(end *state)
	after = func(end *state) {
		if shape.post != nil {
			// The post statement may continue in more than one state.
			post := shape.post
			shape.post = nil
			v.stmt(post, end, ctrl{}, after)
			shape.post = post
			return
		}
		if shape.limit != nil {
			next := logic.Add(counter, logic.IntLit(1))
			if shape.step != nil {
				next = shape.step(end, counter)
			}
			shape.bind(end, next)
		}
		checkInvariants(end, "loop invariant may not be preserved")
		if before != nil {
			v.check(end, nil, logic.Lt(v.intTerm(spec.variant, v.bodyEnv(end, at)), before), shape.pos,
				"loop variant may not decrease: %s", spec.variant.text)
		}
	}
	v.seq(shape.body.List, shape.body.Lbrace, shape.body.Rbrace, head, ctrl{brk: k, cont: after}, after)
}

func (v *fnVerifier) forStmt(s *ast.ForStmt, spec *loopSpec, st *state, k func(*state)) {
	if s.Init != nil {
		// The initializer may continue in more than one state.
		v.stmt(s.Init, st, ctrl{}, func(next *state) {
			without := *s
			without.Init = nil
			v.forStmt(&without, spec, next, k)
		})
		return
	}
	if spec.variant == nil {
		v.report(s.Pos(), "loop needs a //@ Variant annotation to prove that it terminates")
	}
	shape := loopShape{pos: s.Pos(), body: s.Body, post: s.Post, spec: spec, always: s.Cond == nil}
	shape.effects = v.effects(s.Body, s.Post)
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
	ranged := v.info.TypeOf(s.X)
	sort, single := sortOf(ranged)
	switch {
	case single && sort == logic.Int:
		count := v.expr(s.X, st, nil)
		shape.limit = logic.Ite(logic.Le(logic.IntLit(0), count), count, logic.IntLit(0))
		shape.bind = func(st *state, counter *logic.Term) {
			if key != nil {
				st.vals[key] = value{counter}
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
				st.vals[key] = value{counter}
			}
			if element != nil {
				st.vals[element] = v.unknown("char", element.Type(), st)
			}
		}
	case isSlice(ranged):
		header := v.eval(s.X, st, nil)
		shape.limit = header[2]
		shape.bind = func(st *state, counter *logic.Term) {
			if key != nil {
				st.vals[key] = value{counter}
			}
			if element == nil {
				return
			}
			current, ok := v.element(st, st.mem, header, ranged, counter)
			if !ok {
				v.unsupported(s.X.Pos(), fmt.Sprintf("slices of %s are not supported", elemType(ranged)))
			}
			st.vals[element] = current
		}
	default:
		v.unsupported(s.X.Pos(), fmt.Sprintf("range over %s is not supported", ranged))
	}
	v.loop(shape, st, k)
}
