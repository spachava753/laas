package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// variable returns the current value of a variable.
func (v *fnVerifier) variable(id *ast.Ident, st *state) value {
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	if val := st.vals[variable]; val != nil {
		return val
	}
	if v.sentinels[variable] {
		sentinel := logic.Const("var "+variable.Name(), logic.Err)
		st.assume(logic.Not(logic.IsNil(sentinel)))
		return value{sentinel}
	}
	v.unsupported(id.Pos(), id.Name+" is not a local variable of a supported type")
	return nil
}

func (v *fnVerifier) checkIndex(st *state, guard []*logic.Term, length, index *logic.Term, pos token.Pos) {
	v.check(st, guard, logic.Le(logic.IntLit(0), index), pos, "index may be negative")
	v.check(st, guard, logic.Lt(index, length), pos, "index may be out of range")
}

// checkNil requires a pointer that is about to be followed not to be nil.
func (v *fnVerifier) checkNil(st *state, guard []*logic.Term, ref *logic.Term, pos token.Pos) {
	v.check(st, guard, logic.Lt(logic.IntLit(0), ref), pos, "pointer may be nil")
}

// expr evaluates an expression whose value is a single leaf.
func (v *fnVerifier) expr(e ast.Expr, st *state, guard []*logic.Term) *logic.Term {
	val := v.eval(e, st, guard)
	if len(val) != 1 {
		v.unsupported(e.Pos(), fmt.Sprintf("a value of type %s cannot be used here", v.info.TypeOf(e)))
	}
	return val[0]
}

// eval evaluates an expression, checking on the way that it cannot panic.
// guard holds the conditions under which the expression is evaluated at all,
// which matters on the right of && and ||.
func (v *fnVerifier) eval(e ast.Expr, st *state, guard []*logic.Term) value {
	t := v.info.TypeOf(e)
	if _, ok := layoutOf(t); !ok {
		v.unsupported(e.Pos(), fmt.Sprintf("expressions of type %s are not supported", t))
	}
	if tv := v.info.Types[e]; tv.Value != nil {
		sort, _ := sortOf(t)
		return value{v.constant(tv.Value, sort, e, st)}
	}
	switch e := e.(type) {
	case *ast.ParenExpr:
		return v.eval(e.X, st, guard)
	case *ast.Ident:
		return v.variable(e, st)
	case *ast.StarExpr:
		object, ok := pointee(v.info.TypeOf(e.X))
		if !ok {
			break
		}
		ref := v.expr(e.X, st, guard)
		v.checkNil(st, guard, ref, e.Pos())
		return v.object(st, object, ref)
	case *ast.UnaryExpr:
		return v.unary(e, st, guard)
	case *ast.BinaryExpr:
		return value{v.binaryExpr(e, st, guard)}
	case *ast.IndexExpr:
		return v.indexExpr(e, st, guard)
	case *ast.SliceExpr:
		return v.sliceExpr(e, st, guard)
	case *ast.SelectorExpr:
		// The field selection x.f follows a pointer where x is one, which
		// must then not be nil.
		selection := v.info.Selections[e]
		if selection == nil || selection.Kind() != types.FieldVal {
			v.unsupported(e.Pos(), "only fields can be selected; variables of other packages and method values are not supported")
		}
		return v.fields(v.eval(e.X, st, guard), v.info.TypeOf(e.X), selection.Index(), st, guard, e.Sel.Pos())
	case *ast.CompositeLit:
		return v.literal(e, t, st, guard)
	case *ast.CallExpr:
		return v.callExpr(e, st, guard)
	}
	v.unsupported(e.Pos(), "this expression is not supported")
	return nil
}

// evalAs evaluates an expression that is assigned to something of type want.
// It differs from eval only for nil, which has no type of its own.
func (v *fnVerifier) evalAs(e ast.Expr, want types.Type, st *state, guard []*logic.Term) value {
	if !v.isNil(e) {
		// An error value is only ever an error, nil, or the result of a
		// call. Converting anything else to an error would hide a value
		// behind an interface whose methods are not verified.
		if isError(want) && !isError(v.info.TypeOf(e)) {
			v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to an error is not supported", v.info.TypeOf(e)))
		}
		return v.eval(e, st, guard)
	}
	_, isPointer := pointee(want)
	if !isError(want) && !isSlice(want) && !isPointer {
		v.unsupported(e.Pos(), fmt.Sprintf("nil of type %s is not supported", want))
	}
	return zeroValue(want)
}

// object reads every field of the object a pointer refers to.
func (v *fnVerifier) object(st *state, t types.Type, ref *logic.Term) value {
	leaves, _ := layoutOf(t)
	val := make(value, len(leaves))
	for i, lf := range leaves {
		val[i] = v.cell(st, st.mem, typeKey(t)+lf.path, lf, ref)
	}
	v.noteTyped(st, val, t)
	return val
}

// newObject creates an object holding the given value and returns the
// pointer to it.
func (v *fnVerifier) newObject(st *state, t types.Type, val value) value {
	ref := v.alloc(st, v.pass.TypesSizes.Sizeof(t) > 0)
	leaves, _ := layoutOf(t)
	for i, lf := range leaves {
		st.storeCell(typeKey(t)+lf.path, lf, ref, val[i])
	}
	return value{ref}
}

// unary evaluates a unary operator. The only address that can be taken is
// that of a new struct, &T{...}: a pointer to a local variable or into the
// middle of an object would be a second name for storage that already has
// one.
func (v *fnVerifier) unary(e *ast.UnaryExpr, st *state, guard []*logic.Term) value {
	if e.Op == token.AND {
		lit, ok := ast.Unparen(e.X).(*ast.CompositeLit)
		t := v.info.TypeOf(e.X)
		if _, isStruct := t.Underlying().(*types.Struct); !ok || !isStruct {
			v.unsupported(e.Pos(), fmt.Sprintf("taking the address of %s is not supported; only &T{...} creates a pointer", types.ExprString(e.X)))
		}
		return v.newObject(st, t, v.literal(lit, t, st, guard))
	}
	operand := v.expr(e.X, st, guard)
	switch e.Op {
	case token.SUB:
		if operand.Sort == logic.Float {
			return value{v.opaque(e.Op, operand)}
		}
		v.checkFits(st, guard, logic.Neg(operand), v.info.TypeOf(e), e.Pos(), "negation")
		return value{logic.Neg(operand)}
	case token.ADD:
		return value{operand}
	case token.NOT:
		return value{logic.Not(operand)}
	}
	v.unsupported(e.Pos(), fmt.Sprintf("operator %s is not supported", e.Op))
	return nil
}

// binaryExpr evaluates a binary operator. A comparison with nil asks the one
// thing known about an error, whether a pointer refers to anything, or
// whether a slice has an array.
func (v *fnVerifier) binaryExpr(e *ast.BinaryExpr, st *state, guard []*logic.Term) *logic.Term {
	if nilX, nilY := v.isNil(e.X), v.isNil(e.Y); (nilX || nilY) && (e.Op == token.EQL || e.Op == token.NEQ) {
		other := e.X
		if nilX {
			other = e.Y
		}
		t := v.info.TypeOf(other)
		val := v.eval(other, st, guard)
		_, isPointer := pointee(t)
		var isNil *logic.Term
		switch {
		case isError(t):
			isNil = logic.IsNil(val[0])
		case isPointer, isSlice(t):
			isNil = logic.Eq(val[0], logic.RefLit(0))
		default:
			v.unsupported(e.Pos(), fmt.Sprintf("comparing a %s with nil is not supported", t))
		}
		if e.Op == token.NEQ {
			return logic.Not(isNil)
		}
		return isNil
	}
	if object, isPointer := pointee(v.info.TypeOf(e.X)); isPointer && v.pass.TypesSizes.Sizeof(object) == 0 {
		v.unsupported(e.Pos(), "pointers to values of size zero may or may not be equal, so comparing them is not supported")
	}
	left := v.expr(e.X, st, guard)
	switch e.Op {
	case token.LAND:
		return logic.And(left, v.expr(e.Y, st, append(slices.Clip(guard), left)))
	case token.LOR:
		return logic.Or(left, v.expr(e.Y, st, append(slices.Clip(guard), logic.Not(left))))
	}
	return v.binary(e.Op, left, v.expr(e.Y, st, guard), v.info.TypeOf(e), e.OpPos, st, guard)
}

// indexExpr evaluates s[i] for a slice or a string.
func (v *fnVerifier) indexExpr(e *ast.IndexExpr, st *state, guard []*logic.Term) value {
	t := v.info.TypeOf(e.X)
	switch {
	case isString(t):
		text, index := v.expr(e.X, st, guard), v.expr(e.Index, st, guard)
		v.checkIndex(st, guard, logic.Len(text), index, e.Pos())
		char := logic.Select(text, index)
		st.assume(logic.Implies(logic.And(guard...), v.typeFact(char, v.info.TypeOf(e))))
		return value{char}
	case isSlice(t):
		header, index := v.eval(e.X, st, guard), v.expr(e.Index, st, guard)
		v.checkIndex(st, guard, header[2], index, e.Pos())
		element, ok := v.element(st, st.mem, header, t, index)
		if !ok {
			break
		}
		return element
	}
	v.unsupported(e.X.Pos(), fmt.Sprintf("indexing a %s is not supported", t))
	return nil
}

// sliceExpr evaluates s[lo:hi] and s[lo:hi:max]. Slicing a slice yields a
// slice of the same array: no element is copied, and a write through either
// is seen through the other.
func (v *fnVerifier) sliceExpr(e *ast.SliceExpr, st *state, guard []*logic.Term) value {
	t := v.info.TypeOf(e.X)
	if isString(t) {
		return value{v.substring(e, st, guard)}
	}
	if !isSlice(t) {
		v.unsupported(e.Pos(), fmt.Sprintf("slicing a %s is not supported", t))
	}
	header := v.eval(e.X, st, guard)
	bound := func(e ast.Expr, missing *logic.Term) *logic.Term {
		if e == nil {
			return missing
		}
		return v.expr(e, st, guard)
	}
	lo, hi, limit := bound(e.Low, logic.IntLit(0)), bound(e.High, header[2]), bound(e.Max, header[3])
	within := logic.And(logic.Le(logic.IntLit(0), lo), logic.Le(lo, hi), logic.Le(hi, limit), logic.Le(limit, header[3]))
	v.check(st, guard, within, e.Pos(), "slice bounds may be out of range")
	return value{header[0], logic.Add(header[1], lo), logic.Sub(hi, lo), logic.Sub(limit, lo)}
}

// fields follows a path of field indices from a value.
func (v *fnVerifier) fields(cur value, t types.Type, path []int, st *state, guard []*logic.Term, pos token.Pos) value {
	for _, index := range path {
		_, viaPointer := pointee(t)
		if viaPointer {
			v.checkNil(st, guard, cur[0], pos)
		}
		next, fieldType, ok := v.member(st, st.mem, cur, t, index)
		if !ok {
			v.unsupported(pos, fmt.Sprintf("this field has type %s, which is not supported", fieldType))
		}
		cur, t = next, fieldType
	}
	return cur
}

// literal evaluates a composite literal: a struct value, a new slice, or,
// where the & is left out inside another literal, a new object.
func (v *fnVerifier) literal(e *ast.CompositeLit, t types.Type, st *state, guard []*logic.Term) value {
	if object, ok := pointee(t); ok {
		return v.newObject(st, object, v.literal(e, object, st, guard))
	}
	switch u := t.Underlying().(type) {
	case *types.Struct:
		val := zeroValue(t)
		for i, element := range e.Elts {
			index, initial := i, element
			if pair, keyed := element.(*ast.KeyValueExpr); keyed {
				name := pair.Key.(*ast.Ident).Name
				index = slices.IndexFunc(slices.Collect(u.Fields()), func(field *types.Var) bool { return field.Name() == name })
				initial = pair.Value
			}
			lo, _, ok := fieldLeaves(t, index)
			if !ok {
				v.unsupported(element.Pos(), fmt.Sprintf("field %s has unsupported type %s", u.Field(index).Name(), u.Field(index).Type()))
			}
			copy(val[lo:], v.evalAs(initial, u.Field(index).Type(), st, guard))
		}
		return val
	case *types.Slice:
		leaves, ok := layoutOf(u.Elem())
		if !ok {
			v.unsupported(e.Pos(), fmt.Sprintf("slices of %s are not supported", u.Elem()))
		}
		rows := make([]*logic.Term, len(leaves))
		for i, lf := range leaves {
			rows[i] = logic.Fill(logic.IntLit(0), zeroLeaf(lf))
		}
		for _, element := range e.Elts {
			if _, keyed := element.(*ast.KeyValueExpr); keyed {
				v.unsupported(element.Pos(), "keyed slice literals are not supported")
			}
			val := v.evalAs(element, u.Elem(), st, guard)
			for i := range leaves {
				rows[i] = logic.Push(rows[i], val[i])
			}
		}
		length := logic.IntLit(int64(len(e.Elts)))
		return v.allocSlice(st, u.Elem(), rows, length, length)
	}
	v.unsupported(e.Pos(), fmt.Sprintf("literals of type %s are not supported", t))
	return nil
}

// callExpr evaluates a call used as a value: a built-in, a conversion, or a
// call to a function with a single result.
func (v *fnVerifier) callExpr(e *ast.CallExpr, st *state, guard []*logic.Term) value {
	builtin := func(name string) bool { return isBuiltin(v.info, e, name) }
	switch {
	case builtin("len"), builtin("cap"):
		operand := v.eval(e.Args[0], st, guard)
		switch {
		case len(operand) == 1:
			return value{logic.Len(operand[0])}
		case builtin("len"):
			return value{operand[2]}
		}
		return value{operand[3]}
	case builtin("min"), builtin("max"):
		result := v.expr(e.Args[0], st, guard)
		for _, arg := range e.Args[1:] {
			other := v.expr(arg, st, guard)
			smaller := logic.Le(result, other)
			if builtin("max") {
				smaller = logic.Le(other, result)
			}
			result = logic.Ite(smaller, result, other)
		}
		return value{result}
	case builtin("new"):
		t := v.info.TypeOf(e.Args[0])
		if _, isStruct := t.Underlying().(*types.Struct); !isStruct {
			v.unsupported(e.Pos(), fmt.Sprintf("new(%s) is not supported; only structs can be pointed to", t))
		}
		return v.newObject(st, t, zeroValue(t))
	case builtin("make"):
		return v.makeSlice(e, st, guard)
	case builtin("append"):
		v.unsupported(e.Pos(), "append is only supported as the whole right-hand side of an assignment or as the returned value")
	case v.info.Types[e.Fun].IsType():
		return v.conversion(e, st, guard)
	}
	results := v.call(e, st, guard)
	if len(results) != 1 || results[0] == nil {
		v.unsupported(e.Pos(), "this call does not produce a single supported value")
	}
	return results[0]
}

// makeSlice evaluates make([]T, length) and make([]T, length, capacity).
func (v *fnVerifier) makeSlice(e *ast.CallExpr, st *state, guard []*logic.Term) value {
	t := v.info.TypeOf(e)
	if !isSlice(t) || len(e.Args) < 2 {
		v.unsupported(e.Pos(), "make is only supported for slices with a length")
	}
	leaves, ok := layoutOf(elemType(t))
	if !ok {
		v.unsupported(e.Pos(), fmt.Sprintf("slices of %s are not supported", elemType(t)))
	}
	length := v.expr(e.Args[1], st, guard)
	capacity := length
	v.check(st, guard, logic.Le(logic.IntLit(0), length), e.Args[1].Pos(), "make length may be negative")
	v.checkFits(st, guard, length, types.Typ[types.Int], e.Args[1].Pos(), "make length")
	if len(e.Args) == 3 {
		capacity = v.expr(e.Args[2], st, guard)
		v.check(st, guard, logic.Le(length, capacity), e.Args[2].Pos(), "make capacity may be less than the length")
		v.checkFits(st, guard, capacity, types.Typ[types.Int], e.Args[2].Pos(), "make capacity")
	}
	rows := make([]*logic.Term, len(leaves))
	for i, lf := range leaves {
		rows[i] = logic.Fill(capacity, zeroLeaf(lf))
	}
	return v.allocSlice(st, elemType(t), rows, length, capacity)
}

// conversion evaluates T(x). Conversions between integers must fit the
// target type, and one that involves a float yields an unknown value.
// string(b) and []byte(s) copy, so the result holds the same bytes and
// shares nothing with the operand. Any other conversion must leave the value
// as it is.
func (v *fnVerifier) conversion(e *ast.CallExpr, st *state, guard []*logic.Term) value {
	from, to := v.info.TypeOf(e.Args[0]), v.info.TypeOf(e)
	bytes := func(t types.Type) bool {
		return isSlice(t) && types.Identical(elemType(t).Underlying(), types.Typ[types.Uint8])
	}
	switch {
	case v.isNil(e.Args[0]):
		return v.evalAs(e.Args[0], to, st, guard)
	case bytes(from) && isString(to):
		text, _ := v.view(st, st.mem, v.eval(e.Args[0], st, guard), from)
		return value{text}
	case isString(from) && bytes(to):
		// Go does not say how much capacity the new array has.
		text := v.expr(e.Args[0], st, guard)
		roomy := v.fresh("cap", logic.Int)
		_, most, _ := v.intRange(types.Typ[types.Int])
		st.assume(logic.And(logic.Le(logic.Len(text), roomy), logic.Le(roomy, logic.BigLit(most))))
		return v.allocSlice(st, elemType(to), []*logic.Term{text}, logic.Len(text), roomy)
	}
	val := v.evalAs(e.Args[0], to, st, guard)
	source, isScalar := sortOf(from)
	target, _ := sortOf(to)
	numeric := func(sort logic.Sort) bool { return sort == logic.Int || sort == logic.Float }
	switch {
	case isScalar && numeric(source) && numeric(target) && (source == logic.Float || target == logic.Float):
		// Nothing is known about a float, so nothing is known about what
		// it converts to or from, beyond the type of the result.
		return v.unknown("converted", to, st)
	case isScalar && source == logic.Int && target == logic.Int:
		v.check(st, guard, v.typeFact(val[0], to), e.Pos(), "conversion may not fit %s", types.TypeString(to, nil))
		return val
	case types.Identical(from, to), isError(to):
		return val
	}
	if _, isPointer := from.Underlying().(*types.Pointer); !isPointer && types.IdenticalIgnoreTags(from.Underlying(), to.Underlying()) {
		return val
	}
	v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to a %s is not supported", from, to))
	return nil
}
