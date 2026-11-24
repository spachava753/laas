package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"slices"
	"strings"

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
	// expr is the expression assigned to.
	expr ast.Expr
	text string
	// owned is set when what is assigned is an owned field (owns.go).
	owned *ownedStore
	// local and lo locate the leaves of a placeLocal inside its variable.
	local *types.Var
	lo    int
	// A placeMem starts from a pointer, from a slice and an index, or from
	// a variable that lives in memory. cells are the cells of what is
	// assigned and offset is where it starts, both counted from the start of
	// the struct pointed to, of the element, or of the variable. declares is
	// set when the assignment creates the variable.
	box          *types.Var
	global       *types.Var
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
		switch {
		case ok && v.isAssigned(variable):
			// The storage of an assigned package-level variable.
			lv.kind, lv.global, lv.typ, lv.cells = placeMem, variable, variable.Type(), v.globalCells(variable)
			lv.leaves = mustLayout(variable.Type())
			return lv
		case ok && packageVariableOf(variable, "") != nil:
			v.unsupported(e.Pos(), fmt.Sprintf("%s is a package-level variable, which a verified function cannot assign yet", e.Name))
		case !ok || variable.Pkg() != v.pass.Pkg:
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
		v.unsupported(lv.pos, fmt.Sprintf("%s has unsupported type %s%s", lv.text, lv.typ, unsupportedHint(lv.typ)))
	}
	return lv
}

// fieldPlace determines the storage of a field selection x.f: part of the
// struct x points to, or part of wherever the struct x itself is stored.
func (v *fnVerifier) fieldPlace(e *ast.SelectorExpr) lvalue {
	selection := v.info.Selections[e]
	if variable, ok := v.info.Uses[e.Sel].(*types.Var); ok && selection == nil && v.isAssigned(variable) {
		lv := lvalue{pos: e.Pos(), text: types.ExprString(e), expr: e}
		lv.kind, lv.global, lv.typ, lv.cells = placeMem, variable, variable.Type(), v.globalCells(variable)
		lv.leaves = mustLayout(variable.Type())
		return lv
	}
	if variable, ok := v.info.Uses[e.Sel].(*types.Var); ok && selection == nil && variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope() {
		v.unsupported(e.Pos(), fmt.Sprintf("%s is a package-level variable of package %s, and assigning one is not supported yet",
			types.ExprString(e), variable.Pkg().Path()))
	}
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
		lv.owned = nil
		if ownedFieldAt(lv.typ, index) {
			lv.owned = &ownedStore{holder: lv.typ, index: index, off: lv.offset}
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
	lv.expr = e
	switch {
	case lv.global != nil:
		v.noteGlobal(st, lv.global)
		lv.ref, lv.at = globalRef(lv.global), logic.IntLit(0)
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

// loadRecorded returns the current value of an assignment target without
// evaluating its operands a second time. Reading memory is recorded in the
// unit; start is the number of events before the operands of the target
// were evaluated.
func (v *fnVerifier) loadRecorded(lv lvalue, st *state, guard []*logic.Term, start int) value {
	switch lv.kind {
	case placeLocal:
		whole := st.vals[lv.local]
		if whole == nil {
			v.unsupported(lv.pos, "this operand cannot be read and updated in place")
		}
		if _, captured := v.captured[lv.local]; captured {
			return v.readCapturedPart(st, guard, start, lv.local, lv.lo, len(lv.leaves), lv.text, lv.pos)
		}
		return whole[lv.lo : lv.lo+len(lv.leaves)]
	case placeMem, placeMap:
		return v.readAt(st, guard, start, lv.text, lv.pos, func(sink *state, mem memory) value {
			return v.loadIn(lv, sink, mem)
		})
	}
	v.unsupported(lv.pos, "this operand cannot be read and updated in place")
	return nil
}

// loadIn reads what an assignment target in memory holds in some memory.
func (v *fnVerifier) loadIn(lv lvalue, sink *state, mem memory) value {
	if lv.kind == placeMap {
		return v.mapValue(sink, mem, lv.mapType, lv.ref, lv.at)
	}
	val := v.fetch(sink, mem, lv.cells, lv.ref, lv.at)
	v.noteTyped(sink, val, lv.typ)
	v.noteReached(sink, lv.cells, lv.ref, lv.at, lv.typ, lv.typ)
	return val
}

// store performs an assignment in the symbolic state. A write to memory must
// be one the function is allowed to make.
func (v *fnVerifier) store(lv lvalue, val value, st *state) {
	checkGrowth(val)
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
		// which may therefore write it, unless a trusted function that runs
		// this code may write it too.
		w := written{ref: lv.ref, parts: stretchesOf(lv.cells, lv.at)}
		if lv.box == nil {
			v.checkWriteOr(st, nil, w, lv.pos, lv.text+" is assigned", "", v.notListable(lv.expr, lv.pos))
		} else {
			v.checkNotForbidden(st, nil, w, lv.pos, lv.text+" is assigned")
		}
		var written types.Type
		switch {
		case lv.box != nil:
			written = lv.box.Type()
		case lv.pointer != nil:
			written, _ = pointee(v.info.TypeOf(lv.pointer))
		case lv.slice != nil:
			written = elemType(v.info.TypeOf(lv.slice))
		}
		if written != nil && isStructType(written) {
			v.noteStruct(st, structValue{t: written, ref: lv.ref, at: lv.at})
		}
		v.put(st, lv.cells, lv.ref, lv.at, val)
	case placeMap:
		v.mapStore(st, lv.mapType, lv.ref, lv.at, val, true, lv.pos, lv.text+" is assigned")
	}
}

// assign executes an assignment. The operands of the targets and the
// right-hand sides are evaluated first, as one unit, and only then are the
// targets updated, in order. An append as the right-hand side continues
// once for each way it can turn out, and ends the unit itself.
func (v *fnVerifier) assign(s *ast.AssignStmt, st *state, k func(*state)) {
	before := st.brk
	v.openUnit(st)
	targets := make([]lvalue, len(s.Lhs))
	for i, lhs := range s.Lhs {
		// A variable bound to a literal has no value; its calls run the
		// literal.
		if v.isBoundLiteral(lhs) {
			targets[i] = lvalue{kind: placeBlank}
			continue
		}
		v.refuseWriteThrough(lhs)
		targets[i] = v.lvalue(lhs, st, nil)
	}
	simple := s.Tok == token.ASSIGN || s.Tok == token.DEFINE
	var values []value
	switch {
	case !simple:
		op := map[token.Token]token.Token{
			token.ADD_ASSIGN: token.ADD, token.SUB_ASSIGN: token.SUB, token.MUL_ASSIGN: token.MUL,
			token.QUO_ASSIGN: token.QUO, token.REM_ASSIGN: token.REM,
			token.SHL_ASSIGN: token.SHL, token.SHR_ASSIGN: token.SHR, token.AND_ASSIGN: token.AND,
			token.OR_ASSIGN: token.OR, token.XOR_ASSIGN: token.XOR, token.AND_NOT_ASSIGN: token.AND_NOT,
		}[s.Tok]
		// x op= y reads x once, as one of the operands.
		current := v.loadRecorded(targets[0], st, nil, 0)
		operand := v.expr(s.Rhs[0], st, nil)
		if _, single := sortOf(targets[0].typ); !single {
			v.unsupported(s.Pos(), fmt.Sprintf("operator %s is not supported here", s.Tok))
		}
		values = []value{{v.binary(op, current[0], operand, v.info.TypeOf(s.Lhs[0]), s.TokPos, st, nil)}}
	case len(s.Rhs) == 1 && len(s.Lhs) == 1 && v.isAppend(s.Rhs[0]):
		v.appendTo(ast.Unparen(s.Rhs[0]).(*ast.CallExpr), st, func(next *state, result value) {
			v.checkOwnedTarget(next, targets[0], result, s.Rhs[0], before)
			v.followStore(next, targets[0], result)
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
		start := v.unit.events
		ref, key := v.expr(read.X, st, nil), v.evalAs(read.Index, keyType, st, nil)[0]
		v.unit.starts = append(v.unit.starts, start)
		both := v.readAt(st, nil, start, types.ExprString(read), read.Pos(), func(sink *state, mem memory) value {
			return append(slices.Clone(v.mapValue(sink, mem, t, ref, key)), v.mapHas(sink, mem, t, ref, key))
		})
		v.unit.starts = v.unit.starts[:len(v.unit.starts)-1]
		values = []value{both[:len(both)-1], both[len(both)-1:]}
	case len(s.Rhs) == 1 && len(s.Lhs) > 1:
		values = v.callResults(s.Rhs[0], st, wanted(targets))
	default:
		for i, rhs := range s.Rhs {
			if v.isBoundLiteral(s.Lhs[i]) {
				values = append(values, nil)
				continue
			}
			values = append(values, v.evalAs(rhs, v.targetType(targets[i], rhs), st, nil))
		}
	}
	v.closeUnit(st)
	for i, target := range targets {
		var rhs ast.Expr
		if len(s.Rhs) == len(s.Lhs) {
			rhs = s.Rhs[i]
		} else if len(s.Rhs) == 1 && !v.isMapRead(s.Rhs[0]) {
			rhs = s.Rhs[0]
		}
		v.checkOwnedTarget(st, target, values[i], rhs, before)
		v.followStore(st, target, values[i])
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
	if _, asserted := ast.Unparen(e).(*ast.TypeAssertExpr); asserted {
		v.unsupported(e.Pos(), ifaceAsserted)
	}
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
	defer v.begin()()
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

// appendTo evaluates append(s, values...) and append(s, t...). Go writes
// the new elements into the array of s when its capacity allows, where
// every other slice of that array sees them, and otherwise copies
// everything to a new array. Which of the two happens is often unknown, so
// execution continues once for each. Writing in place is a write like any
// other: the function must be allowed to modify the capacity of s.
//
// With ..., the elements added are those of the slice t, or the bytes of
// the string t when s is a []byte. Go copies them as memmove does, so when t
// shares the array of s what is added is what t held before the write.
func (v *fnVerifier) appendTo(call *ast.CallExpr, st *state, k func(*state, value)) {
	t := v.info.TypeOf(call)
	elem := elemType(t)
	if _, ok := layoutOf(elem); !ok {
		v.unsupported(call.Pos(), fmt.Sprintf("slices of %s are not supported", elem))
	}
	spread := call.Ellipsis.IsValid()
	// The append runs after its operands. Since it is not ordered like a
	// call, it is ordered after the calls of the targets only by an event
	// among its operands.
	u := v.unit
	operands := u.pushCeiling()
	start, readsBefore := u.events, len(u.reads)
	base := v.evalAs(call.Args[0], t, st, nil)
	var added []value
	var source value
	if spread {
		source = v.eval(call.Args[1], st, nil)
	} else {
		for _, arg := range call.Args[1:] {
			added = append(added, v.evalAs(arg, elem, st, nil))
		}
	}
	u.reach(operands)
	// Each way the append can turn out closes a copy of the unit, and a
	// path that is not taken closes none; the unit is open no longer.
	v.unit = nil
	if !spread && len(added) == 0 {
		v.unit = u
		v.closeUnit(st)
		k(st, base)
		return
	}
	ref, length, capacity := base[0], base[2], base[3]
	cells, step := v.cellsOf(elem), v.span(elem)
	var keys []string
	sorts := map[string]logic.Sort{}
	for _, c := range cells {
		if _, seen := sorts[c.key]; !seen {
			keys = append(keys, c.key)
			sorts[c.key] = c.sort
		}
	}
	// count is how many elements are added, and extent how many positions
	// they take.
	count := logic.IntLit(int64(len(added)))
	fromString := spread && isString(v.info.TypeOf(call.Args[1]))
	switch {
	case fromString:
		count = v.named(st, "len", logic.Len(source[0]))
	case spread:
		count = source[2]
	}
	extent := logic.Mul(count, logic.IntLit(step))
	grown := logic.Add(length, count)
	tName := ""
	if spread {
		tName = types.ExprString(call.Args[1])
	}
	// readSource records the read of what t holds that the append makes,
	// which Go may make before or after the calls of the targets. When
	// before is set, the read comes before the write of this append, which
	// does not move.
	readSource := func(next *state, before bool) {
		if !spread || fromString {
			return
		}
		var c *ceiling
		if before {
			c = v.unit.pushCeiling()
		}
		v.readAt(next, nil, start, "the elements of "+tName+" that append copies", call.Pos(), func(sink *state, mem memory) value {
			copied := make(value, len(keys))
			for i, key := range keys {
				copied[i] = logic.Subseq(v.row(sink, mem, key, sorts[key], source[0]), source[1], logic.Add(source[1], extent))
			}
			return copied
		})
		if before {
			v.unit.reach(c)
		}
	}
	// copyFrom states that row holds, at the positions from at on, the
	// elements of t as they are in the memory of state next, for the region
	// key.
	copyFrom := func(next *state, key string, row, at *logic.Term) {
		index := v.bound("k")
		within := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, extent))
		var from *logic.Term
		if fromString {
			from = logic.Select(source[0], index)
		} else {
			old := logic.Select(next.mem.region(key, logic.SeqOf(logic.SeqOf(sorts[key]))), source[0])
			from = logic.Select(old, logic.Add(source[1], index))
		}
		next.assume(logic.Forall(index, logic.Implies(within, v.same(logic.Select(row, logic.Add(at, index)), from))))
	}
	inPlace := logic.Le(grown, capacity)
	if !v.quickly(st, nil, logic.Not(inPlace)) {
		v.branch(call.Pos())
		next := st.clone()
		next.assume(inPlace)
		at := v.elementAt(base, t, length)
		into := written{ref: ref}
		if spread {
			for _, key := range keys {
				into.parts = append(into.parts, stretch{key: key, lo: at, hi: logic.Add(at, extent)})
			}
		}
		for j := range added {
			into.parts = append(into.parts, stretchesOf(cells, logic.Add(at, logic.IntLit(int64(j)*step)))...)
		}
		v.checkWriteOr(next, nil, into, call.Pos(),
			fmt.Sprintf("append may write into the capacity of %s", types.ExprString(call.Args[0])), "", "")
		v.unit = u.fork()
		readSource(next, true)
		if spread {
			// Every region of the element type gets a new row: the old one
			// outside the positions written, and the elements of t, read
			// before the write, inside them.
			for _, key := range keys {
				before := logic.Select(next.mem.region(key, logic.SeqOf(logic.SeqOf(sorts[key]))), ref)
				row := v.fresh("appended", logic.SeqOf(sorts[key]))
				index := v.bound("k")
				outside := logic.Or(logic.Lt(index, at), logic.Le(logic.Add(at, extent), index))
				next.assume(logic.Forall(index, logic.Implies(outside, v.same(logic.Select(row, index), logic.Select(before, index)))))
				copyFrom(next, key, row, at)
				next.storeRow(key, sorts[key], ref, row)
			}
		}
		for j, element := range added {
			v.put(next, cells, ref, logic.Add(at, logic.IntLit(int64(j)*step)), element)
		}
		if v.unit.events == start {
			// Nothing orders the write after the targets. A call there may
			// run before or after it, which is the same only for a call
			// whose contract changes nothing and reads no memory; and
			// every read there, including those for such a call, may see
			// the write.
			for _, made := range v.unit.calls {
				if !made.pure {
					v.unsupported(made.pos, fmt.Sprintf("%s is called in the target of this assignment, and Go may call it before or after "+
						"append writes into the array of %s; assign the result of %s to a variable in a statement of its own first",
						made.name, types.ExprString(call.Args[0]), made.name))
				}
			}
			for _, r := range v.unit.reads[:readsBefore] {
				r.end = true
			}
		}
		v.unit.wrote(next, "the write of append into the array of "+types.ExprString(call.Args[0]))
		v.closeUnit(next)
		k(next, value{ref, base[1], grown, capacity})
	}
	if !v.quickly(st, nil, inPlace) {
		v.branch(call.Pos())
		next := st.clone()
		next.assume(logic.Lt(capacity, grown))
		// The array to move to must be one that can be allocated. That is
		// proved and not assumed: assuming it would contradict a slice
		// already at the limit and make everything after the append
		// provable. The runtime does not allocate grown elements: it picks
		// a capacity of its own, twice the old one while that is small and
		// a quarter more after, and panics when that capacity in bytes,
		// rounded up to a whole page for a large array, is more than can be
		// allocated, even where grown is not. The old capacity is less than
		// grown, or the slice would not move, so the capacity picked is
		// less than twice grown; no platform has pages of more than 64 KB.
		v.check(next, nil, v.appendFits(grown, elem), call.Pos(), "the slice that append grows may be more than can be allocated, or have a capacity an int cannot hold")
		// Copying the old elements reads them, which may happen before or
		// after the calls of the targets.
		v.unit = u.fork()
		v.unit.starts = append(v.unit.starts, start)
		old := logic.Mul(length, logic.IntLit(step))
		v.readAt(next, nil, start, "the elements of "+types.ExprString(call.Args[0])+" that append copies", call.Pos(),
			func(sink *state, mem memory) value {
				copied := make(value, len(keys))
				for i, key := range keys {
					copied[i] = logic.Subseq(v.row(sink, mem, key, sorts[key], ref), base[1], logic.Add(base[1], old))
				}
				return copied
			})
		readSource(next, false)
		v.closeUnit(next)
		// The new array holds the old elements and the added ones. What
		// lies in its capacity beyond them is not said: it is certainly not
		// what followed the old elements in their array.
		moved := v.alloc(next, v.pass.TypesSizes.Sizeof(elem) > 0)
		for _, key := range keys {
			prev := logic.Select(next.mem.region(key, logic.SeqOf(logic.SeqOf(sorts[key]))), ref)
			row := v.fresh("moved", logic.SeqOf(sorts[key]))
			index := v.bound("k")
			copied := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, old))
			next.assume(logic.Forall(index, logic.Implies(copied, v.same(logic.Select(row, index), logic.Select(prev, logic.Add(base[1], index))))))
			if spread {
				copyFrom(next, key, row, old)
			}
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
	if decl.Tok == token.CONST || decl.Tok == token.TYPE {
		// A type declaration runs nothing. Its type is a type of its own,
		// kept apart from every other by Go's identity of types, which the
		// keys of memory follow; see typeKey.
		return
	}
	for _, spec := range decl.Specs {
		spec := spec.(*ast.ValueSpec)
		v.openUnit(st)
		targets := make([]lvalue, len(spec.Names))
		for i, name := range spec.Names {
			if v.isBoundLiteral(name) {
				targets[i] = lvalue{kind: placeBlank}
				continue
			}
			targets[i] = v.lvalue(name, st, nil)
		}
		var values []value
		switch {
		case len(spec.Values) == 0:
			for _, target := range targets {
				values = append(values, zeroValue(v.targetType(target, nil)))
			}
		case len(spec.Values) == 1 && len(spec.Names) > 1:
			values = v.callResults(spec.Values[0], st, wanted(targets))
		default:
			for i, initial := range spec.Values {
				if v.isBoundLiteral(spec.Names[i]) {
					values = append(values, nil)
					continue
				}
				values = append(values, v.evalAs(initial, v.targetType(targets[i], initial), st, nil))
			}
		}
		v.closeUnit(st)
		for i, target := range targets {
			v.store(target, values[i], st)
		}
	}
}

// returnStmt evaluates the returned values and ends the frame being
// executed, the function or a literal; see returned.
func (v *fnVerifier) returnStmt(s *ast.ReturnStmt, st *state) {
	vars := v.fn.results
	if v.lit != nil {
		vars = slices.Collect(v.lit.sig.Results().Variables())
	}
	if len(s.Results) == 0 {
		v.returned(st, nil, s.Pos())
		return
	}
	results := make([]value, len(vars))
	v.openUnit(st)
	switch {
	case len(s.Results) == 1 && len(results) > 1:
		wants := make([]types.Type, len(vars))
		for i, result := range vars {
			wants[i] = result.Type()
		}
		results = v.callResults(s.Results[0], st, wants)
	case len(s.Results) == 1 && v.isAppend(s.Results[0]):
		v.appendTo(ast.Unparen(s.Results[0]).(*ast.CallExpr), st, func(next *state, result value) {
			v.returned(next, []value{result}, s.Pos())
		})
		return
	default:
		for i, e := range s.Results {
			results[i] = v.evalAs(e, vars[i].Type(), st, nil)
		}
	}
	v.closeUnit(st)
	v.returned(st, results, s.Pos())
}

// atReturn checks the postcondition in a final state, once the results
// have been assigned and the deferred calls have run.
func (v *fnVerifier) atReturn(st *state, results []value, pos token.Pos) {
	// A function that may have changed a group restores its invariants
	// (V3).
	v.proveGroups(st, nil, v.groupsCovered(v.frame, v.varGroups), pos, "on return")
	// The return is recorded with the branches taken to get here, as a
	// possible failure, a possible success, or both; see tieFailures.
	// A return fails if any of its errors is one and succeeds if none is.
	outcome := failure{path: slices.Clip(st.chosen), facts: slices.Clip(st.hyps)}
	var none []*logic.Term
	for _, index := range errorResults(v.fn) {
		if results[index] != nil {
			outcome.errs = append(outcome.errs, results[index][0])
			none = append(none, logic.IsNil(results[index][0]))
		}
	}
	if len(none) > 0 && !v.quickly(st, nil, logic.And(none...)) {
		v.failures = append(v.failures, outcome)
	}
	if len(none) > 0 && !v.quickly(st, nil, logic.Not(logic.And(none...))) {
		v.successes = append(v.successes, outcome)
	}
	env := &specEnv{v: v, sink: st, fn: v.fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: v.entryBrk}
	if v.chooseStates != nil {
		v.chosenEnsures(st, results, pos)
	} else {
		for _, c := range v.fn.ensures {
			v.checkClause(c, env, st, nil, pos, "postcondition may not hold")
		}
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

// appendFits is what an append that moves its slice to a new array must
// prove of grown, the new length: the capacity the runtime picks, less than
// twice grown, rounded up in bytes, is something that can be allocated, and
// is a capacity an int can hold. growslice turns the rounded size back into
// a capacity with int(capmem / size) and checks only maxAlloc, which is
// more than MaxInt on a 32-bit target: there, appending 838374793 bytes of
// a full []byte of 879605573 to itself gives a slice whose cap is
// -2147483648, and no panic (TestBuffers386). So the rounded size must also
// be at most size * MaxInt.
func (v *fnVerifier) appendFits(grown *logic.Term, elem types.Type) *logic.Term {
	size := v.pass.TypesSizes.Sizeof(elem)
	room := logic.Add(logic.Mul(grown, logic.IntLit(2*size)), logic.IntLit(1<<16))
	fits := []*logic.Term{logic.Le(room, logic.BigLit(v.maxAlloc())), v.typeFact(grown, types.Typ[types.Int])}
	if size > 0 {
		_, maxInt, _ := v.intRange(types.Typ[types.Int])
		fits = append(fits, logic.Le(room, logic.BigLit(new(big.Int).Mul(maxInt, big.NewInt(size)))))
	}
	return logic.And(fits...)
}

// chosenEnsures proves the Ensures of the contract of an interface method
// for a value verified code made, whose states are ghost: the method check
// chooses the states of the receiver after the call, so the Ensures is
// proved with the states of the receiver in the memory on return given each
// of their values, joined by Or. The choice is made for each outcome, after
// the results; the states before the call are what the caller's state says,
// of which the implementation knows nothing (F28).
func (v *fnVerifier) chosenEnsures(st *state, results []value, pos token.Pos) {
	states := v.ifaceStatesOf(v.chooseStates.Type())
	at := home(v.entry[v.chooseStates][0])
	before := v.row(nil, st.mem, stateRegion, logic.Bool, at)
	var cases []*logic.Term
	for choice := range 1 << len(states) {
		row := before
		for i, s := range states {
			row = logic.Store(row, s.position(), logic.BoolLit(choice&(1<<i) != 0))
		}
		mem := maps.Clone(st.mem)
		mem[stateRegion] = logic.Store(st.mem.region(stateRegion, logic.SeqOf(logic.BoolSeq)), at, row)
		env := &specEnv{v: v, sink: st, fn: v.fn, args: v.entry, results: results, now: memory{}, post: mem, before: v.entryBrk}
		var all []*logic.Term
		for _, c := range v.fn.ensures {
			all = append(all, v.formula(c, c.node, env))
		}
		cases = append(cases, logic.And(all...))
	}
	var texts []string
	for _, c := range v.fn.ensures {
		texts = append(texts, strings.Join(strings.Fields(c.text), " "))
	}
	phrase, _ := stateNames(states)
	v.check(st, nil, logic.Or(cases...), pos, "postcondition may not hold for any value of %s of %s after the call: %s; the states of a value that verified code made "+
		"are ghost, so its method can only choose them after the call, and cannot know them before it", phrase, v.chooseStates.Name(), strings.Join(texts, " And "))
}
