package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The places a value can be assigned to.
const (
	placeBlank = iota // the blank identifier
	placeLocal        // a local variable, or a field of one that holds a struct
	placeMem          // a struct a pointer points to, an element of a slice, or fields of one of these
	placeMap          // the value a map has for a key
)

// lvalue is an assignment target.
type lvalue struct {
	kind   int
	typ    types.Type // the type of what is assigned
	leaves []leaf
	pos    token.Pos
	text   string
	// local and lo locate the leaves of a placeLocal inside its variable.
	local *types.Var
	lo    int
	// A placeMem starts from a pointer, from a slice and an index, or from
	// a variable that lives in memory. cells are the cells of what is
	// assigned and offset is where it starts, both counted from the start of
	// the struct pointed to, of the element, or of the variable. declares is
	// set when the assignment creates the variable.
	box          *types.Var
	declares     bool
	pointer      ast.Expr
	slice, index ast.Expr
	cells        []cell
	offset       int64
	// mapType is the type of the map of a placeMap, with slice and index
	// holding the map and the key.
	mapType types.Type
	// ref is the allocation or the map, and at the position of the struct
	// or element, or the key, once the target has been evaluated.
	ref, at *logic.Term
}

// place determines what kind of storage an assignment target is, without
// evaluating it.
func (v *fnVerifier) place(e ast.Expr) lvalue {
	e = ast.Unparen(e)
	lv := lvalue{pos: e.Pos(), text: types.ExprString(e)}
	switch e := e.(type) {
	case *ast.Ident:
		if e.Name == "_" {
			return lv
		}
		variable, ok := v.info.ObjectOf(e).(*types.Var)
		if !ok || variable.Parent() == v.pass.Pkg.Scope() || variable.Pkg() != v.pass.Pkg {
			v.unsupported(e.Pos(), fmt.Sprintf("%s is not a local variable", e.Name))
		}
		if v.boxed[variable] {
			lv.kind, lv.box, lv.typ, lv.cells = placeMem, variable, variable.Type(), v.cellsOf(variable.Type())
			break
		}
		lv.kind, lv.local, lv.typ = placeLocal, variable, variable.Type()
	case *ast.StarExpr:
		object, ok := pointee(v.info.TypeOf(e.X))
		if !ok {
			v.unsupported(e.Pos(), fmt.Sprintf("pointers of type %s are not supported", v.info.TypeOf(e.X)))
		}
		lv.kind, lv.pointer, lv.typ, lv.cells = placeMem, e.X, object, v.cellsOf(object)
	case *ast.IndexExpr:
		t := v.info.TypeOf(e.X)
		if isMap(t) && mapModelled(t) {
			_, elem := mapParts(t)
			lv.kind, lv.slice, lv.index, lv.mapType, lv.typ = placeMap, e.X, e.Index, t, elem
			break
		}
		if !isSlice(t) {
			v.unsupported(e.Pos(), fmt.Sprintf("only elements of slices can be assigned, not those of a %s", t))
		}
		lv.kind, lv.slice, lv.index, lv.typ, lv.cells = placeMem, e.X, e.Index, elemType(t), v.cellsOf(elemType(t))
	case *ast.SelectorExpr:
		lv = v.fieldPlace(e)
	default:
		v.unsupported(e.Pos(), "only variables, fields, and slice elements can be assigned")
	}
	var ok bool
	if lv.leaves, ok = layoutOf(lv.typ); !ok {
		v.unsupported(lv.pos, fmt.Sprintf("%s has unsupported type %s", lv.text, lv.typ))
	}
	return lv
}

// fieldPlace determines the storage of a field selection x.f: part of the
// struct x points to, or part of wherever the struct x itself is stored.
func (v *fnVerifier) fieldPlace(e *ast.SelectorExpr) lvalue {
	selection := v.info.Selections[e]
	if selection == nil || selection.Kind() != types.FieldVal {
		v.unsupported(e.Pos(), "only variables, fields, and slice elements can be assigned")
	}
	var lv lvalue
	if object, viaPointer := pointee(v.info.TypeOf(e.X)); viaPointer {
		lv = lvalue{kind: placeMem, pointer: e.X, typ: object, cells: v.cellsOf(object)}
	} else {
		lv = v.place(e.X)
	}
	lv.pos, lv.text = e.Pos(), types.ExprString(e)
	if lv.kind == placeMap {
		v.unsupported(e.Pos(), "a field of a map value cannot be assigned; assign the whole value")
	}
	for _, index := range selection.Index() {
		if _, viaPointer := pointee(lv.typ); viaPointer {
			v.unsupported(e.Pos(), "assigning through an embedded pointer is not supported; name the pointer")
		}
		field := lv.typ.Underlying().(*types.Struct).Field(index)
		lo, hi, ok := fieldLeaves(lv.typ, index)
		if !ok {
			v.unsupported(e.Pos(), fmt.Sprintf("field %s has unsupported type %s", field.Name(), field.Type()))
		}
		if lv.kind == placeMem {
			lv.cells, lv.offset = lv.cells[lo:hi], lv.offset+v.fieldOffset(lv.typ, index)
		}
		lv.lo, lv.typ = lv.lo+lo, field.Type()
	}
	return lv
}

// lvalue resolves an assignment target: the pointer, or the slice and the
// index, it mentions are evaluated, and a nil pointer or an index out of
// range is ruled out. guard holds the conditions under which the target is
// evaluated at all.
func (v *fnVerifier) lvalue(e ast.Expr, st *state, guard []*logic.Term) lvalue {
	lv := v.place(e)
	switch {
	case lv.box != nil:
		// A variable that an assignment creates has no place yet.
		if id, ok := ast.Unparen(e).(*ast.Ident); ok && v.info.Defs[id] != nil {
			lv.declares = true
			break
		}
		held := st.vals[lv.box]
		if held == nil {
			v.unsupported(lv.pos, fmt.Sprintf("%s is used before it is declared", lv.box.Name()))
		}
		lv.ref, lv.at = held[0], held[1]
	case lv.kind == placeMem && lv.pointer != nil:
		pointer := v.eval(lv.pointer, st, guard)
		v.checkNil(st, guard, pointer[0], lv.pos)
		lv.ref, lv.at = pointer[0], pointer[1]
	case lv.kind == placeMem:
		header, index := v.eval(lv.slice, st, guard), v.expr(lv.index, st, guard)
		v.checkIndex(st, guard, header[2], index, lv.pos)
		// A slice that has an element has an array.
		st.assume(logic.Implies(logic.And(guard...), logic.Not(logic.Eq(header[0], logic.RefLit(0)))))
		lv.ref, lv.at = header[0], v.elementAt(header, v.info.TypeOf(lv.slice), index)
	case lv.kind == placeMap:
		keyType, _ := mapParts(lv.mapType)
		lv.ref, lv.at = v.expr(lv.slice, st, guard), v.evalAs(lv.index, keyType, st, guard)[0]
	}
	return lv
}

// bounds returns the positions the cells of a place cover, counted like the
// cells themselves.
func bounds(cells []cell) (lo, hi int64) {
	for i, c := range cells {
		if i == 0 || c.off < lo {
			lo = c.off
		}
		hi = max(hi, c.off+1)
	}
	return lo, hi
}

// load returns the current value of an assignment target without evaluating
// its operands a second time.
func (v *fnVerifier) load(lv lvalue, st *state) value {
	switch lv.kind {
	case placeLocal:
		whole := st.vals[lv.local]
		if whole == nil {
			v.unsupported(lv.pos, "this operand cannot be read and updated in place")
		}
		return whole[lv.lo : lv.lo+len(lv.leaves)]
	case placeMem:
		val := v.fetch(st, st.mem, lv.cells, lv.ref, lv.at)
		v.noteTyped(st, val, lv.typ)
		return val
	case placeMap:
		return v.mapValue(st, st.mem, lv.mapType, lv.ref, lv.at)
	}
	v.unsupported(lv.pos, "this operand cannot be read and updated in place")
	return nil
}

// store performs an assignment in the symbolic state. A write to memory must
// be one the function is allowed to make.
func (v *fnVerifier) store(lv lvalue, val value, st *state) {
	if lv.kind != placeBlank && len(val) != len(lv.leaves) {
		v.unsupported(lv.pos, fmt.Sprintf("a value of this type cannot be assigned to %s", lv.text))
	}
	switch lv.kind {
	case placeLocal:
		// Values are shared between states, so the variable gets a new one.
		whole := slices.Clone(st.vals[lv.local])
		if whole == nil {
			whole = zeroValue(lv.local.Type())
		}
		copy(whole[lv.lo:], val)
		st.vals[lv.local] = whole
	case placeMem:
		if lv.declares {
			v.bind(st, lv.box, val)
			break
		}
		// A variable that lives in memory was created by this function,
		// which may therefore write it.
		if lv.box == nil {
			v.checkWrite(st, nil, written{ref: lv.ref, parts: stretchesOf(lv.cells, lv.at)}, lv.pos, lv.text+" is assigned")
		}
		v.put(st, lv.cells, lv.ref, lv.at, val)
	case placeMap:
		v.mapStore(st, lv.mapType, lv.ref, lv.at, val, true, lv.pos, lv.text+" is assigned")
	}
}

// assign executes an assignment. The operands of the targets and the
// right-hand sides are evaluated first, and only then are the targets
// updated, in order. The relative order of those evaluations only matters
// when one of them modifies memory, which is ruled out: a call that does is
// allowed only as the whole right-hand side of an assignment to variables.
// An append is such a right-hand side too, and continues once for each way
// it can turn out.
func (v *fnVerifier) assign(s *ast.AssignStmt, st *state, k func(*state)) {
	targets := make([]lvalue, len(s.Lhs))
	plain := true
	for i, lhs := range s.Lhs {
		targets[i] = v.lvalue(lhs, st, nil)
		// Where a variable is does not depend on what a call does, whether
		// it is held by the verifier or lives in memory.
		plain = plain && (targets[i].kind <= placeLocal || targets[i].box != nil)
	}
	simple := s.Tok == token.ASSIGN || s.Tok == token.DEFINE
	v.effectful = nil
	if len(s.Rhs) == 1 && plain && simple {
		v.allowEffects(s.Rhs[0])
	}
	var values []value
	switch {
	case !simple:
		op := map[token.Token]token.Token{
			token.ADD_ASSIGN: token.ADD, token.SUB_ASSIGN: token.SUB, token.MUL_ASSIGN: token.MUL,
			token.QUO_ASSIGN: token.QUO, token.REM_ASSIGN: token.REM,
		}[s.Tok]
		current, operand := v.load(targets[0], st), v.expr(s.Rhs[0], st, nil)
		if _, single := sortOf(targets[0].typ); !single {
			v.unsupported(s.Pos(), fmt.Sprintf("operator %s is not supported here", s.Tok))
		}
		values = []value{{v.binary(op, current[0], operand, v.info.TypeOf(s.Lhs[0]), s.TokPos, st, nil)}}
	case len(s.Rhs) == 1 && len(s.Lhs) == 1 && v.isAppend(s.Rhs[0]):
		v.appendTo(ast.Unparen(s.Rhs[0]).(*ast.CallExpr), st, func(next *state, result value) {
			v.store(targets[0], result, next)
			k(next)
		})
		return
	case len(s.Rhs) == 1 && len(s.Lhs) == 2 && v.isMapRead(s.Rhs[0]):
		// v, ok := m[k]
		read := ast.Unparen(s.Rhs[0]).(*ast.IndexExpr)
		t := v.info.TypeOf(read.X)
		keyType, elem := mapParts(t)
		// As for the results of a call, the value must have the type of
		// what it is assigned to.
		if want := wanted(targets)[0]; want != nil && !types.Identical(want, elem) {
			v.unsupported(s.Pos(), fmt.Sprintf("converting a %s to a %s is not supported here; assign the value to a variable of its own type first", elem, want))
		}
		ref, key := v.expr(read.X, st, nil), v.evalAs(read.Index, keyType, st, nil)[0]
		values = []value{v.mapValue(st, st.mem, t, ref, key), {v.mapHas(st, st.mem, t, ref, key)}}
	case len(s.Rhs) == 1 && len(s.Lhs) > 1:
		values = v.callResults(s.Rhs[0], st, wanted(targets))
	default:
		for i, rhs := range s.Rhs {
			values = append(values, v.evalAs(rhs, v.targetType(targets[i], rhs), st, nil))
		}
	}
	for i, target := range targets {
		v.store(target, values[i], st)
	}
	k(st)
}

// targetType returns the type a right-hand side is converted to on
// assignment, which matters for nil.
func (v *fnVerifier) targetType(target lvalue, rhs ast.Expr) types.Type {
	if target.kind == placeBlank {
		return v.info.TypeOf(rhs)
	}
	return target.typ
}

// isMapRead reports whether an expression reads a map of a modelled type.
func (v *fnVerifier) isMapRead(e ast.Expr) bool {
	read, ok := ast.Unparen(e).(*ast.IndexExpr)
	if !ok {
		return false
	}
	t := v.info.TypeOf(read.X)
	return isMap(t) && mapModelled(t)
}

func (v *fnVerifier) isAppend(e ast.Expr) bool {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	return ok && isBuiltin(v.info, call, "append")
}

// callResults evaluates a call whose results are assigned one by one to
// things of the given types, nil for the blank identifier. Each result must
// have the type it is assigned to: Go would convert it otherwise, and a
// pointer or struct that becomes an error is a value the verifier does not
// follow.
func (v *fnVerifier) callResults(e ast.Expr, st *state, wants []types.Type) []value {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok {
		v.unsupported(e.Pos(), "multi-value expressions other than function calls are not supported")
	}
	if tuple, isTuple := v.info.TypeOf(call).(*types.Tuple); isTuple {
		for i := range min(tuple.Len(), len(wants)) {
			if have := tuple.At(i).Type(); wants[i] != nil && !types.Identical(have, wants[i]) {
				v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to a %s is not supported here; assign the result to a variable of its own type first", have, wants[i]))
			}
		}
	}
	return v.call(call, st, nil)
}

// wanted lists the types of assignment targets, nil for the blank identifier.
func wanted(targets []lvalue) []types.Type {
	wants := make([]types.Type, len(targets))
	for i, target := range targets {
		if target.kind != placeBlank {
			wants[i] = target.typ
		}
	}
	return wants
}

// appendTo evaluates append(s, values...). Go writes the new elements into
// the array of s when its capacity allows, where every other slice of that
// array sees them, and otherwise copies everything to a new array. Which of
// the two happens is often unknown, so execution continues once for each.
// Writing in place is a write like any other: the function must be allowed
// to modify the capacity of s.
func (v *fnVerifier) appendTo(call *ast.CallExpr, st *state, k func(*state, value)) {
	if call.Ellipsis.IsValid() {
		v.unsupported(call.Pos(), "append(s, t...) is not supported yet")
	}
	t := v.info.TypeOf(call)
	elem := elemType(t)
	if _, ok := layoutOf(elem); !ok {
		v.unsupported(call.Pos(), fmt.Sprintf("slices of %s are not supported", elem))
	}
	base := v.evalAs(call.Args[0], t, st, nil)
	var added []value
	for _, arg := range call.Args[1:] {
		added = append(added, v.evalAs(arg, elem, st, nil))
	}
	if len(added) == 0 {
		k(st, base)
		return
	}
	ref, length, capacity := base[0], base[2], base[3]
	grown := logic.Add(length, logic.IntLit(int64(len(added))))
	cells, step := v.cellsOf(elem), v.span(elem)
	var keys []string
	sorts := map[string]logic.Sort{}
	for _, c := range cells {
		if _, seen := sorts[c.key]; !seen {
			keys = append(keys, c.key)
			sorts[c.key] = c.sort
		}
	}
	inPlace := logic.Le(grown, capacity)
	if !v.quickly(st, nil, logic.Not(inPlace)) {
		v.branch(call.Pos())
		next := st.clone()
		next.assume(inPlace)
		start := v.elementAt(base, t, length)
		into := written{ref: ref}
		for j := range added {
			into.parts = append(into.parts, stretchesOf(cells, logic.Add(start, logic.IntLit(int64(j)*step)))...)
		}
		v.checkWrite(next, nil, into, call.Pos(),
			fmt.Sprintf("append may write into the capacity of %s", types.ExprString(call.Args[0])))
		for j, element := range added {
			v.put(next, cells, ref, logic.Add(start, logic.IntLit(int64(j)*step)), element)
		}
		k(next, value{ref, base[1], grown, capacity})
	}
	if !v.quickly(st, nil, inPlace) {
		v.branch(call.Pos())
		next := st.clone()
		next.assume(logic.Lt(capacity, grown))
		// The array to move to must be one that can be allocated. That is
		// proved and not assumed: assuming it would contradict a slice
		// already at the limit and make everything after the append
		// provable.
		v.checkAlloc(next, nil, grown, elem, call.Pos(), "the slice append grows")
		// The new array holds the old elements and the added ones. What
		// lies in its capacity beyond them is not said: it is certainly not
		// what followed the old elements in their array.
		moved := v.alloc(next, v.pass.TypesSizes.Sizeof(elem) > 0)
		for _, key := range keys {
			old := logic.Select(next.mem.region(key, logic.SeqOf(logic.SeqOf(sorts[key]))), ref)
			row := v.fresh("moved", logic.SeqOf(sorts[key]))
			index := v.bound("k")
			copied := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, logic.Mul(length, logic.IntLit(step))))
			next.assume(logic.Forall(index, logic.Implies(copied, v.same(logic.Select(row, index), logic.Select(old, logic.Add(base[1], index))))))
			next.storeRow(key, sorts[key], moved, row)
		}
		for j, element := range added {
			v.put(next, cells, moved, logic.Mul(logic.Add(length, logic.IntLit(int64(j))), logic.IntLit(step)), element)
		}
		result := value{moved, logic.IntLit(0), grown, v.fresh("cap", logic.Int)}
		next.assume(v.wellFormed(result, t, next.brk))
		k(next, result)
	}
}

// declare executes a local var declaration: variables without an initial
// value get the zero value of their type, the others are assigned like an
// ordinary assignment. Local constants need no state.
func (v *fnVerifier) declare(s *ast.DeclStmt, st *state) {
	decl := s.Decl.(*ast.GenDecl)
	if decl.Tok == token.CONST {
		return
	}
	if decl.Tok != token.VAR {
		v.unsupported(s.Pos(), "local type declarations are not supported")
	}
	for _, spec := range decl.Specs {
		spec := spec.(*ast.ValueSpec)
		targets := make([]lvalue, len(spec.Names))
		for i, name := range spec.Names {
			targets[i] = v.lvalue(name, st, nil)
		}
		var values []value
		v.effectful = nil
		switch {
		case len(spec.Values) == 0:
			for _, target := range targets {
				values = append(values, zeroValue(v.targetType(target, nil)))
			}
		case len(spec.Values) == 1 && len(spec.Names) > 1:
			v.allowEffects(spec.Values[0])
			values = v.callResults(spec.Values[0], st, wanted(targets))
		default:
			if len(spec.Values) == 1 {
				v.allowEffects(spec.Values[0])
			}
			for i, initial := range spec.Values {
				values = append(values, v.evalAs(initial, v.targetType(targets[i], initial), st, nil))
			}
		}
		for i, target := range targets {
			v.store(target, values[i], st)
		}
	}
}

// returnStmt evaluates the returned values and checks the postcondition.
func (v *fnVerifier) returnStmt(s *ast.ReturnStmt, st *state) {
	results := make([]value, len(v.fn.results))
	v.effectful = nil
	if len(s.Results) == 1 {
		v.allowEffects(s.Results[0])
	}
	switch {
	case len(s.Results) == 0:
		for i, result := range v.fn.results {
			results[i] = v.current(st, result)
		}
	case len(s.Results) == 1 && len(results) > 1:
		wants := make([]types.Type, len(v.fn.results))
		for i, result := range v.fn.results {
			wants[i] = result.Type()
		}
		results = v.callResults(s.Results[0], st, wants)
	case len(s.Results) == 1 && v.isAppend(s.Results[0]):
		v.appendTo(ast.Unparen(s.Results[0]).(*ast.CallExpr), st, func(next *state, result value) {
			v.atReturn(next, []value{result}, s.Pos())
		})
		return
	default:
		for i, e := range s.Results {
			results[i] = v.evalAs(e, v.fn.results[i].Type(), st, nil)
		}
	}
	v.atReturn(st, results, s.Pos())
}

// atReturn checks the postcondition in a final state.
func (v *fnVerifier) atReturn(st *state, results []value, pos token.Pos) {
	// Returning assigns the results to the result variables. Only one that
	// lives in memory can be seen afterwards, through a pointer to it.
	for i, result := range v.fn.results {
		if held := st.vals[result]; v.boxed[result] && held != nil && results[i] != nil {
			v.put(st, v.cellsOf(result.Type()), held[0], held[1], results[i])
		}
	}
	env := &specEnv{v: v, sink: st, fn: v.fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: v.entryBrk}
	for _, c := range v.fn.ensures {
		v.checkClause(c, env, st, nil, pos, "postcondition may not hold")
	}
	// The caller gets back what it passed by pointer, and the results,
	// with their invariants intact.
	// A struct passed by value is the caller's own again too: what it
	// refers to is shared, so its invariant is checked for the value it had
	// on entry against memory as it is now.
	for _, param := range v.fn.params {
		if v.entry[param] != nil {
			v.checkInvariants(st, nil, st.mem, v.entry[param], param.Type(), pos, describe(param)+" on return")
		}
	}
	for i, result := range v.fn.results {
		if results[i] == nil {
			continue
		}
		// A result is described by the name annotations use for it.
		what := "the result"
		for name, index := range v.fn.resultNames {
			if index == i && name != "result" {
				what = "the result " + name
			}
		}
		v.checkInvariants(st, nil, st.mem, results[i], result.Type(), pos, what)
	}
}

// bodyEnv gives meaning to the names in an annotation inside the function
// body, at the given position.
func (v *fnVerifier) bodyEnv(st *state, pos token.Pos) *specEnv {
	return &specEnv{v: v, sink: st, st: st, pos: pos, now: st.mem}
}
