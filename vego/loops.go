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
	// row is set when the site may write every state of an interface
	// value, at the home of the value root holds, and fp when it may write
	// the footprint of that value. owner is the type of the pointer root
	// holds when it points to an owner.
	row   bool
	fp    bool
	owner types.Type
	// ownerOff is where the owner lies from where root points, as for
	// &p.out of a strings.Builder held inline (F14 of the review of
	// d32bbee).
	ownerOff int64
}

// effects describes what a loop may change.
type effects struct {
	// whole holds the variables the loop assigns, and grown those among
	// them whose every assignment has the form x = append(x, ...).
	whole map[*types.Var]bool
	grown map[*types.Var]bool
	sites []site
	// owners holds, for stores into owned fields, the owner each is rooted
	// at, as sites with no cells whose root, owner, and ownerOff are set;
	// they write nothing of their own, and only tell the head of the loop
	// which owners grow (owns.go).
	owners []site
	// deletes holds every call of delete the loop may run, in its body or
	// in a literal it calls.
	deletes []*ast.CallExpr
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

// fieldHolder returns the variable that an argument passes a pointer into,
// for a parameter of the given pointer type, and the offset of the
// pointer from where the variable points: the argument is &x.f.g, or x.f.g
// where Go takes the address for a pointer receiver, x is a local variable
// that holds a pointer to a struct, and every selection is of a field of a
// struct held in the one before, not behind another pointer.
func (v *fnVerifier) fieldHolder(arg ast.Expr, want types.Type) (*types.Var, int64, bool) {
	arg = ast.Unparen(arg)
	if address, ok := arg.(*ast.UnaryExpr); ok && address.Op == token.AND {
		arg = ast.Unparen(address.X)
	}
	if t := v.info.TypeOf(arg); t == nil || !types.Identical(types.NewPointer(t), want) {
		return nil, 0, false
	}
	var offset int64
	for {
		sel, ok := arg.(*ast.SelectorExpr)
		if !ok {
			return nil, 0, false
		}
		selection := v.info.Selections[sel]
		if selection == nil || selection.Kind() != types.FieldVal {
			return nil, 0, false
		}
		object := selection.Recv()
		pointer, viaPointer := pointee(object)
		if viaPointer {
			object = pointer
		}
		// A promoted field takes one step for each struct on the way,
		// none of which may be a pointer.
		for _, index := range selection.Index() {
			u, isStruct := object.Underlying().(*types.Struct)
			if !isStruct {
				return nil, 0, false
			}
			offset += v.fieldOffset(object, index)
			object = u.Field(index).Type()
		}
		inner := ast.Unparen(sel.X)
		if viaPointer {
			variable := v.localVar(inner)
			if variable == nil || v.boxed[variable] {
				return nil, 0, false
			}
			return variable, offset, true
		}
		arg = inner
	}
}

// effects computes what a loop may change: the variables it assigns and the
// memory it may write, directly or through a call.
func (v *fnVerifier) effects(nodes ...ast.Node) *effects {
	eff := &effects{whole: map[*types.Var]bool{}, grown: map[*types.Var]bool{}}
	otherwise := map[*types.Var]bool{}
	assigned := func(e ast.Expr, appendedTo *types.Var) {
		if e == nil || v.isBoundLiteral(e) {
			return
		}
		lv := v.place(e)
		switch {
		case lv.global != nil:
			// The storage of an assigned package-level variable, in regions
			// of its own.
			lo, hi := bounds(lv.cells)
			eff.sites = append(eff.sites, site{cells: lv.cells, lo: lo, hi: hi})
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
			// A store into an owned field keeps what the owner owns placed,
			// as a call that writes an owner does: the head states it of
			// the owner at the root.
			if lv.owned != nil {
				if root, owner, off, ok := v.ownerRoot(lv.pointer, lv.owned); ok {
					eff.owners = append(eff.owners, site{root: root, owner: owner, ownerOff: off})
				}
			}
		case lv.kind == placeMem:
			eff.sites = append(eff.sites, site{cells: lv.cells, elem: elemType(v.info.TypeOf(lv.slice)), root: v.localVar(lv.slice)})
		case lv.kind == placeMap:
			eff.sites = append(eff.sites, site{mapType: lv.mapType, root: v.localVar(lv.slice)})
		}
	}
	// The body of a literal runs where it is called, so a loop that calls
	// one changes what the body changes. A literal written inside the loop
	// is walked where it is written; one bound outside is walked at its
	// calls, once.
	walked := map[*ast.FuncLit]bool{}
	var visit func(n ast.Node) bool
	visit = func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			if walked[n] {
				return false
			}
			walked[n] = true
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
			if lit := v.literalOf(n); lit != nil && !walked[lit] {
				ast.Inspect(lit, visit)
			}
			if isBuiltin(v.info, n, "delete") && isMap(v.info.TypeOf(n.Args[0])) {
				eff.sites = append(eff.sites, site{mapType: v.info.TypeOf(n.Args[0]), root: v.localVar(n.Args[0])})
				eff.deletes = append(eff.deletes, n)
			}
			v.callSites(n, eff)
			// What is handed over runs during the call: a literal is walked
			// where it is written, anything else writes what its contract
			// lists.
			for _, arg := range v.pkgVerifier.handedArgs(n) {
				if _, isLit := ast.Unparen(arg).(*ast.FuncLit); isLit {
					continue
				}
				if contract := v.handedContract(arg); contract != nil {
					v.handedSites(arg, contract, eff)
				}
			}
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
	callee := v.pkgVerifier.calleeAt(call)
	method, value := throughValue(v.info, call)
	var fn *funcInfo
	switch {
	case v.literalOf(call) != nil:
		// The body of the literal is walked where it is called.
		return
	case value:
		// A call through a function value writes what the Modifies of its
		// type lists.
		fn = v.valueContract(v.info.TypeOf(call.Fun))
	case method != nil:
		// So does a call through an interface value, by the Modifies of
		// the method.
		fn = v.methodContract(method)
	case callee == nil || errorConstructor(callee):
		return
	default:
		fn = v.contractOf(callee)
	}
	if fn == nil {
		return
	}
	// A call whose contract cannot be relied on ends its path, where it is
	// reported, so the loop needs nothing of it; one that relies on part of
	// it writes what that part lists. See viewOf.
	view := v.viewOf(fn)
	if view.cut {
		return
	}
	fn = view.fn
	// What code of the package the call may run writes (F7).
	forms, _ := v.reachedTargets(call, fn, nil, nil)
	for _, form := range forms {
		v.callSitesOf(eff, form, nil)
	}
	sig := fn.obj.Type().(*types.Signature)
	if callee != nil {
		sig = callee.Type().(*types.Signature)
	}
	// A call into a buffer or a Writer formatted into writes what the
	// writer's own Write lists, of the writer as it is; see prints.go.
	if writer, write := v.printedInto(call, fn); writer != nil {
		fn, sig = write, write.obj.Type().(*types.Signature)
		for _, m := range fn.modifies {
			form, _, err := v.locateTarget(fn, m, nil, nil, nil)
			if err != nil {
				v.misread(m.clause, err)
			}
			at := site{cells: form.cells, elem: form.elem, mapType: form.mapType, lo: form.lo, hi: form.hi}
			if form.owner {
				eff.sites = append(eff.sites, v.ownedSites(form.typ, map[types.Type]bool{})...)
			}
			if form.direct && fn.paramNames[m.name] == fn.params[0] {
				v.rootSite(&at, writer, form)
			}
			eff.sites = append(eff.sites, at)
		}
		return
	}
	argument := func(param *types.Var) ast.Expr {
		if param == sig.Recv() || (param != nil && param == fn.receiver) {
			sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
			if selection := v.info.Selections[sel]; ok && selection != nil && len(selection.Index()) == 1 {
				return sel.X
			}
			return nil
		}
		// A pack is a new slice, which no expression names; what it is
		// rooted at is not known, and the write is forgotten by region.
		bound, _ := bindArgs(v.info, call, paramsOf(sig), sig.Variadic())
		for _, b := range bound {
			if b.param == param && !b.packed {
				return b.expr
			}
		}
		return nil
	}
	for _, m := range fn.modifies {
		first, _, err := v.locateTarget(fn, m, nil, nil, nil)
		if err != nil {
			v.misread(m.clause, err)
		}
		for _, form := range append([]shape{first}, first.also...) {
			v.callSitesOf(eff, form, argument)
		}
	}
}

// callSitesOf adds to eff the site of one shape of a Modifies entry of a
// call, rooted at the argument it names when one does.
func (v *fnVerifier) callSitesOf(eff *effects, form shape, argument func(*types.Var) ast.Expr) {
	{
		at := site{cells: form.cells, elem: form.elem, mapType: form.mapType, lo: form.lo, hi: form.hi, row: form.row, fp: form.fp}
		if form.param == nil {
			// The storage of a package-level variable, or what it refers
			// to: no argument names it.
			if form.owner {
				eff.sites = append(eff.sites, v.ownedSites(form.typ, map[types.Type]bool{})...)
			}
			eff.sites = append(eff.sites, at)
			return
		}
		if form.row || form.fp {
			// An interface value held in a variable that the loop does not
			// assign keeps its home.
			if arg := argument(form.param); form.direct && arg != nil {
				if variable := v.localVar(arg); variable != nil && !v.boxed[variable] && isIface(variable.Type()) {
					at.root = variable
				}
			}
			eff.sites = append(eff.sites, at)
			return
		}
		// What an owner's fields refer to may change too, wherever it
		// lies: the loop forgets it by region.
		if form.owner {
			eff.sites = append(eff.sites, v.ownedSites(form.typ, map[types.Type]bool{})...)
		}
		// Only a pointer or slice passed as it is names the same object
		// before and inside the call.
		if arg := argument(form.param); form.direct && arg != nil {
			v.rootSite(&at, arg, form)
			// An owner read through an owned pointer field of a variable,
			// as s.store, grows within what the variable's owner owns.
			if form.owner && at.root == nil {
				if root, owner, ok := v.ownedPathRoot(arg); ok {
					eff.owners = append(eff.owners, site{root: root, owner: owner})
				}
			}
		}
		eff.sites = append(eff.sites, at)
	}
}

// rootSite roots a site of a call at the variable that holds what is
// passed for the parameter a Modifies clause names, as it is passed: the
// pointer or slice itself, or a pointer to a field of what a variable
// points to, as the receiver of h.mu.Lock() is, which names that field
// before and inside the call, at its offset. An owner so rooted is
// recorded with where it lies from the root, so that the head of the loop
// states that what it owns grows only by what the loop creates; see
// forget.
func (v *fnVerifier) rootSite(at *site, arg ast.Expr, form shape) {
	at.root = v.holder(arg, form.param.Type())
	offset := int64(0)
	if at.root == nil && form.elem == nil && form.mapType == nil {
		if root, off, ok := v.fieldHolder(arg, form.param.Type()); ok {
			offset = off
			at.root, at.lo, at.hi = root, at.lo+offset, at.hi+offset
			at.cells = slices.Clone(at.cells)
			for i := range at.cells {
				at.cells[i].off += offset
			}
		}
	}
	if form.owner && at.root != nil && at.lo == offset {
		at.owner, at.ownerOff = form.typ, offset
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
	// A site that writes a footprint may write every region, also those
	// not yet in memory, which an epoch covers; see footprint.go.
	var footprints []target
	preciseFootprints := true
	for _, at := range eff.sites {
		if !at.fp {
			continue
		}
		val := st.vals[at.root]
		if at.root == nil || val == nil || eff.whole[at.root] {
			preciseFootprints = false
			continue
		}
		footprints = append(footprints, target{fp: true, ref: home(val[0]), rows: st.mem.region(footprintRegion, footprintSort)})
	}
	writesFootprints := !preciseFootprints || len(footprints) > 0
	for _, at := range eff.sites {
		if at.fp && !at.row {
			continue
		}
		val := st.vals[at.root]
		precise := at.root != nil && val != nil && (!eff.whole[at.root] || (at.elem != nil && eff.grown[at.root]))
		t := target{cells: at.cells, elem: at.elem, mapType: at.mapType, row: at.row}
		switch {
		case !precise:
		case at.row:
			t.ref, t.row = home(val[0]), true
		case at.mapType != nil:
			t.ref = val[0]
		case at.elem != nil:
			t.ref, t.lo = val[0], val[1]
			t.hi = logic.Add(val[1], logic.Mul(val[3], logic.IntLit(v.span(at.elem))))
		default:
			// The cells are counted from where the pointer points, which
			// is where a single target starts.
			t.ref, t.lo, t.hi, t.single = val[0], val[1], logic.Add(val[1], logic.IntLit(at.hi)), true
			// The struct the root points to, or the variable whose address
			// is taken, which lies at the root's position.
			struct_ := at.root.Type()
			if object, isPointer := pointee(struct_); isPointer {
				struct_ = object
			}
			if isStructType(struct_) {
				t.base = &structValue{t: struct_, ref: val[0], at: val[1]}
			}
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
	if writesFootprints {
		for key, region := range st.mem {
			if key == epochKey || key == footprintRegion || isVarRegion(key) {
				continue
			}
			if regions[key] == nil {
				flat := !region.Sort.Elem().IsSeq()
				leafSort := region.Sort.Elem()
				if !flat {
					leafSort = leafSort.Elem()
				}
				regions[key] = &writes{sort: leafSort, precise: true, flat: flat}
			}
			regions[key].precise = regions[key].precise && preciseFootprints
			regions[key].targets = append(regions[key].targets, footprints...)
		}
	}
	for _, key := range slices.Sorted(maps.Keys(regions)) {
		written := regions[key]
		sort := logic.SeqOf(logic.SeqOf(written.sort))
		if written.flat {
			sort = logic.SeqOf(written.sort)
		}
		known := &layer{prev: st.mem.region(key, sort), bound: st.brk, targets: written.targets, flat: written.flat, key: key}
		if !written.precise {
			known.bound, known.targets = v.entryBrk, v.frameReaching(key)
		}
		forgotten := v.fresh("mem'"+key, sort)
		v.layers[forgotten.Name] = known
		head.mem[key] = forgotten
	}
	// What an owner held in a variable the loop does not assign owns grows
	// only by what the loop creates, since every call that changes it
	// does; with the owner's struct forgotten, this is what keeps its
	// fields placed.
	for _, at := range slices.Concat(eff.sites, eff.owners) {
		if val := st.vals[at.root]; at.owner != nil && val != nil && !eff.whole[at.root] {
			owner := value{val[0], logic.Add(val[1], logic.IntLit(at.ownerOff))}
			head.assume(v.ownerGrowth(head, st.mem, head.mem, owner, at.owner, st.brk))
		}
	}
	if !writesFootprints {
		// What an iteration creates may be part of a footprint afterwards.
		grown := v.grow(head, st.brk, nil)
		grown.after = head.brk
	}
	if writesFootprints {
		// Every region not yet in memory starts from the epoch, and the
		// footprints grow only by what the loop creates.
		e := v.fresh("epoch", logic.Int)
		if preciseFootprints {
			v.epochs[e.Name] = &epoch{before: st.mem, bound: st.brk, targets: footprints}
		} else {
			v.epochs[e.Name] = &epoch{before: st.mem, bound: v.entryBrk, targets: v.frameReaching("")}
		}
		head.mem[epochKey] = e
		grown := v.grow(head, st.brk, nil)
		grown.after = head.brk
	}
	return head
}

// frameReaching returns the Modifies targets that reach into a region, a
// footprint reaching into every one; for key "", the targets that may
// reach into any region.
func (v *fnVerifier) frameReaching(key string) []target {
	var reaching []target
	for _, t := range v.frame {
		if t.fp || key == "" || t.reaches([]string{key}) {
			reaching = append(reaching, t)
		}
	}
	return reaching
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
	// enter is called with the state at the head of an arbitrary
	// iteration, before its body, and leave once the body has been
	// verified on every path. runs, when set, gives the condition under
	// which an iteration runs its body: an iteration whose condition fails
	// goes on to the next one without it.
	enter func(head *state)
	leave func()
	runs  func(head *state) *logic.Term
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
			v.checkClauseFramed(c, v.bodyEnv(st, at), st, nil, shape.pos, what, func(node *logic.Node, goal *logic.Term) bool {
				return v.framedLoop(st, at, c, node, goal)
			})
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
		v.assumeKeeping(head, c, v.bodyEnv(head, at), "the head of the loop at "+v.placeOf(shape.pos))
	}
	// A frame may preserve them from here (framedLoop): the head is kept
	// as it is once they are assumed, which every path of the body
	// continues.
	assumed := head.clone()
	for _, c := range spec.invariants {
		head.loops = append(head.loops, &loopKept{c: c, head: assumed, at: at})
	}
	// What is known of the unknowns at the head: their types, and the
	// invariants, on every path that comes to the loop; see tieFailures.
	summary := &forward{facts: slices.Clip(head.hyps[len(st.hyps):])}
	for _, taken := range st.chosen {
		summary.path = append(summary.path, taken.cond)
	}
	// The variant is measured where the invariants hold, before the
	// condition is evaluated, so that it must decrease across the condition
	// and the body together: a condition that writes memory could otherwise
	// undo what the body did.
	var before *logic.Term
	if spec.variant != nil {
		before = v.intTerm(spec.variant, v.bodyEnv(head, at))
	}
	// The condition is evaluated once more than the body runs: the loop is
	// left in the state after that last evaluation.
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
	if before != nil {
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
		// tieFailures. They are taken in the order of their names, so that
		// the questions tieFailures asks come in the same order every run.
		for _, name := range slices.Sorted(maps.Keys(forgotten)) {
			lost := forgotten[name]
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
			// The post statement may continue in more than one state. No
			// statement can be put before it, so no read in it is shown
			// as one to move there.
			v.unsplit = true
			v.stmt(shape.post, end, ctrl{}, func(next *state) {
				v.unsplit = false
				finish(next)
			})
			v.unsplit = false
			return
		}
		finish(end)
	}
	if shape.runs != nil {
		body := shape.runs(head)
		skipped := head.clone()
		skipped.decide(logic.Not(body))
		finish(skipped)
		head.decide(body)
	}
	if shape.enter != nil {
		shape.enter(head)
		defer shape.leave()
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
	// What the condition writes is forgotten at the head too.
	shape.effects = v.effects(s.Cond, s.Body, s.Post)
	for _, variable := range renewed {
		shape.effects.whole[variable] = true
	}
	shape.cond = func(st *state) *logic.Term {
		if s.Cond == nil {
			return logic.True()
		}
		var cond *logic.Term
		v.evaluateSometimes(st, func() { cond = v.expr(s.Cond, st, nil) })
		return cond
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
	// The range expression is evaluated once, before the first iteration.
	// What it reads of memory is read in the same unit.
	v.openUnit(st)
	switch {
	case single && sort == logic.Int:
		count := v.expr(s.X, st, nil)
		v.closeUnit(st)
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
		v.closeUnit(st)
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
		// A map is walked in one order of the keys it has at the start,
		// which nobody knows; see visited.go. What the loop may change of
		// a map of the type while it runs is checked where it changes it.
		ref := v.expr(s.X, st, nil)
		v.closeUnit(st)
		walk := v.startMapRange(st, ranged, ref, s.Pos(), types.ExprString(s.X))
		active := &activeRange{walk: walk, at: s.Pos(), text: types.ExprString(s.X), frame: v.lit,
			skips: v.deletesOtherKeys(shape.effects, ranged, key)}
		shape.limit = walk.n0
		// The key and position of each state's iteration, which enter
		// takes for the iteration whose body is verified.
		positions := map[*state][2]*logic.Term{}
		shape.bind = func(st *state, counter *logic.Term) {
			at, number, position := v.enterPosition(st, walk, counter)
			positions[st] = [2]*logic.Term{number, position}
			if !active.skips {
				// No key the loop has not reached is deleted, so the key
				// of the position is in the map; see deletesOtherKeys.
				st.assume(logic.Implies(logic.Lt(position, walk.n0), v.mapHas(st, st.mem, ranged, ref, at)))
			}
			if spec.visited != nil {
				st.visited = maps.Clone(st.visited)
				if st.visited == nil {
					st.visited = map[*clause]*visitedSet{}
				}
				st.visited[spec.visited] = &visitedSet{r: walk, counter: position}
			}
			if key != nil {
				v.bind(st, key, value{at})
			}
			if element != nil {
				v.bind(st, element, v.mapValue(st, st.mem, ranged, ref, at))
			}
		}
		if active.skips {
			// A key deleted before the loop reached it is not visited: its
			// position runs no body.
			shape.runs = func(head *state) *logic.Term {
				number := positions[head][0]
				return logic.Select(v.row(head, head.mem, mapOwner(ranged)+hasLeaf.path, hasLeaf.sort, ref), number)
			}
		}
		shape.enter = func(head *state) {
			active.number, active.position = positions[head][0], positions[head][1]
			v.ranges = append(v.ranges, active)
		}
		shape.leave = func() { v.ranges = v.ranges[:len(v.ranges)-1] }
		// Leaving the loop by break, or after the last iteration, leaves
		// the range.
		outer := k
		k = func(st *state) {
			saved := v.ranges
			v.ranges = slices.DeleteFunc(slices.Clone(v.ranges), func(r *activeRange) bool { return r == active })
			outer(st)
			v.ranges = saved
		}
	case isSlice(ranged):
		header := v.eval(s.X, st, nil)
		v.closeUnit(st)
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
