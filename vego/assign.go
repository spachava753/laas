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
	placeField        // fields of the object a pointer refers to
	placeElem         // an element of a slice, or fields of one
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
	// owner is the struct type of the object, or the element type of the
	// slice, and prefix the path of the assigned part inside it. base is the
	// expression for the pointer or the slice, and index for the element.
	owner  types.Type
	prefix string
	base   ast.Expr
	index  ast.Expr
	// ref is the object or backing array, and at the position in the array,
	// once the target has been evaluated.
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
		lv.kind, lv.local, lv.typ = placeLocal, variable, variable.Type()
	case *ast.StarExpr:
		object, ok := pointee(v.info.TypeOf(e.X))
		if !ok {
			v.unsupported(e.Pos(), fmt.Sprintf("pointers of type %s are not supported", v.info.TypeOf(e.X)))
		}
		lv.kind, lv.base, lv.owner, lv.typ = placeField, e.X, object, object
	case *ast.IndexExpr:
		t := v.info.TypeOf(e.X)
		if !isSlice(t) {
			v.unsupported(e.Pos(), fmt.Sprintf("only elements of slices can be assigned, not those of a %s", t))
		}
		lv.kind, lv.base, lv.index, lv.owner, lv.typ = placeElem, e.X, e.Index, elemType(t), elemType(t)
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
// object x points to, or part of wherever the struct x itself is stored.
func (v *fnVerifier) fieldPlace(e *ast.SelectorExpr) lvalue {
	selection := v.info.Selections[e]
	if selection == nil || selection.Kind() != types.FieldVal {
		v.unsupported(e.Pos(), "only variables, fields, and slice elements can be assigned")
	}
	var lv lvalue
	if object, viaPointer := pointee(v.info.TypeOf(e.X)); viaPointer {
		lv = lvalue{kind: placeField, base: e.X, owner: object, typ: object}
	} else {
		lv = v.place(e.X)
	}
	lv.pos, lv.text = e.Pos(), types.ExprString(e)
	for _, index := range selection.Index() {
		if _, viaPointer := pointee(lv.typ); viaPointer {
			v.unsupported(e.Pos(), "assigning through an embedded pointer is not supported; name the pointer")
		}
		field := lv.typ.Underlying().(*types.Struct).Field(index)
		lo, _, ok := fieldLeaves(lv.typ, index)
		if !ok {
			v.unsupported(e.Pos(), fmt.Sprintf("field %s has unsupported type %s", field.Name(), field.Type()))
		}
		lv.lo, lv.prefix, lv.typ = lv.lo+lo, lv.prefix+"."+field.Name(), field.Type()
	}
	return lv
}

// lvalue resolves an assignment target: the pointer or the slice and the
// index it mentions are evaluated, and a nil pointer or an index out of
// range is ruled out.
func (v *fnVerifier) lvalue(e ast.Expr, st *state) lvalue {
	lv := v.place(e)
	switch lv.kind {
	case placeField:
		lv.ref = v.expr(lv.base, st, nil)
		v.checkNil(st, nil, lv.ref, lv.pos)
	case placeElem:
		header, index := v.eval(lv.base, st, nil), v.expr(lv.index, st, nil)
		v.checkIndex(st, nil, header[2], index, lv.pos)
		lv.ref, lv.at = header[0], logic.Add(header[1], index)
	}
	return lv
}

// key returns the key of the region that holds one leaf of the target.
func (lv lvalue) key(lf leaf) string {
	if lv.kind == placeElem {
		return "[]" + typeKey(lv.owner) + lv.prefix + lf.path
	}
	return typeKey(lv.owner) + lv.prefix + lf.path
}

// load returns the current value of an assignment target without evaluating
// its operands a second time.
func (v *fnVerifier) load(lv lvalue, st *state) value {
	var val value
	switch lv.kind {
	case placeLocal:
		whole := st.vals[lv.local]
		if whole == nil {
			v.unsupported(lv.pos, "this operand cannot be read and updated in place")
		}
		return whole[lv.lo : lv.lo+len(lv.leaves)]
	case placeField:
		for _, lf := range lv.leaves {
			val = append(val, v.cell(st, st.mem, lv.key(lf), lf, lv.ref))
		}
	case placeElem:
		for _, lf := range lv.leaves {
			val = append(val, logic.Select(v.row(st, st.mem, lv.key(lf), lf, lv.ref), lv.at))
		}
	default:
		v.unsupported(lv.pos, "this operand cannot be read and updated in place")
	}
	v.noteTyped(st, val, lv.typ)
	return val
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
	case placeField:
		v.checkWrite(st, nil, typeKey(lv.owner)+lv.prefix, lv.ref, nil, nil, lv.pos, lv.text+" is assigned")
		for i, lf := range lv.leaves {
			st.storeCell(lv.key(lf), lf, lv.ref, val[i])
		}
	case placeElem:
		v.checkWrite(st, nil, "[]"+typeKey(lv.owner)+lv.prefix, lv.ref, lv.at, logic.Add(lv.at, logic.IntLit(1)), lv.pos, lv.text+" is assigned")
		for i, lf := range lv.leaves {
			row := logic.Select(st.mem.region(lv.key(lf), logic.SeqOf(logic.SeqOf(lf.sort))), lv.ref)
			st.storeRow(lv.key(lf), lf, lv.ref, logic.Store(row, lv.at, val[i]))
		}
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
		targets[i] = v.lvalue(lhs, st)
		plain = plain && targets[i].kind <= placeLocal
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
	case len(s.Rhs) == 1 && len(s.Lhs) > 1:
		values = v.callResults(s.Rhs[0], st)
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

func (v *fnVerifier) isAppend(e ast.Expr) bool {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	return ok && isBuiltin(v.info, call, "append")
}

func (v *fnVerifier) callResults(e ast.Expr, st *state) []value {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok {
		v.unsupported(e.Pos(), "multi-value expressions other than function calls are not supported")
	}
	return v.call(call, st, nil)
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
	leaves, ok := layoutOf(elem)
	if !ok {
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
	ref, off, length, capacity := base[0], base[1], base[2], base[3]
	grown := logic.Add(length, logic.IntLit(int64(len(added))))
	// The grown length must be proved to fit. Assuming it would contradict a
	// length already at the limit and make everything after the append
	// provable.
	v.checkFits(st, nil, grown, types.Typ[types.Int], call.Pos(), "append length")
	owner := "[]" + typeKey(elem)
	inPlace := logic.Le(grown, capacity)
	if !v.quickly(st, nil, logic.Not(inPlace)) {
		v.branch(call.Pos())
		next := st.clone()
		next.assume(inPlace)
		start := logic.Add(off, length)
		v.checkWrite(next, nil, owner, ref, start, logic.Add(off, grown), call.Pos(),
			fmt.Sprintf("append may write into the capacity of %s", types.ExprString(call.Args[0])))
		for i, lf := range leaves {
			row := logic.Select(next.mem.region(owner+lf.path, logic.SeqOf(logic.SeqOf(lf.sort))), ref)
			for j, element := range added {
				row = logic.Store(row, logic.Add(start, logic.IntLit(int64(j))), element[i])
			}
			next.storeRow(owner+lf.path, lf, ref, row)
		}
		k(next, value{ref, off, grown, capacity})
	}
	if !v.quickly(st, nil, inPlace) {
		v.branch(call.Pos())
		next := st.clone()
		next.assume(logic.Lt(capacity, grown))
		// The new array holds the old elements and the added ones. What
		// lies in its capacity beyond them is not said: it is certainly not
		// what followed the old elements in their array.
		rows := make([]*logic.Term, len(leaves))
		for i, lf := range leaves {
			old := logic.Select(next.mem.region(owner+lf.path, logic.SeqOf(logic.SeqOf(lf.sort))), ref)
			rows[i] = v.fresh("moved", logic.SeqOf(lf.sort))
			index := v.bound("k")
			copied := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, length))
			next.assume(logic.Forall(index, logic.Implies(copied, v.same(logic.Select(rows[i], index), logic.Select(old, logic.Add(off, index))))))
			for j, element := range added {
				next.assume(v.same(logic.Select(rows[i], logic.Add(length, logic.IntLit(int64(j)))), element[i]))
			}
		}
		roomy := v.fresh("cap", logic.Int)
		_, most, _ := v.intRange(types.Typ[types.Int])
		next.assume(logic.And(logic.Le(grown, roomy), logic.Le(roomy, logic.BigLit(most))))
		k(next, v.allocSlice(next, elem, rows, grown, roomy))
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
			targets[i] = v.lvalue(name, st)
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
			values = v.callResults(spec.Values[0], st)
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
			results[i] = st.vals[result]
		}
	case len(s.Results) == 1 && len(results) > 1:
		results = v.callResults(s.Results[0], st)
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
	env := &specEnv{v: v, sink: st, fn: v.fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: v.entryBrk}
	for _, c := range v.fn.ensures {
		v.checkClause(c, env, st, nil, pos, "postcondition may not hold")
	}
}

// bodyEnv gives meaning to the names in an annotation inside the function
// body, at the given position.
func (v *fnVerifier) bodyEnv(st *state, pos token.Pos) *specEnv {
	return &specEnv{v: v, sink: st, st: st, pos: pos, now: st.mem}
}
