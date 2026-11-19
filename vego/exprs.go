package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// variable returns the current value of a variable. One that lives in
// memory is read from there.
func (v *fnVerifier) variable(id *ast.Ident, st *state, guard []*logic.Term) value {
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	if held := st.vals[variable]; held != nil && v.boxed[variable] {
		return v.readAt(st, guard, v.unit.start(), id.Name, id.Pos(), func(sink *state, mem memory) value {
			return v.pointedIn(sink, mem, variable.Type(), held)
		})
	}
	if val := v.current(st, variable); val != nil {
		return val
	}
	if variable != nil && variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope() && isError(variable.Type()) {
		return v.errorVariable(variable, id.Pos(), st)
	}
	v.unsupported(id.Pos(), id.Name+" is not a local variable of a supported type")
	return nil
}

// errorVariable reads a package-level error variable, which must be a
// sentinel.
func (v *fnVerifier) errorVariable(variable *types.Var, pos token.Pos, st *state) value {
	sentinel, why := v.sentinelTerm(st, variable)
	if why != "" {
		v.unsupported(pos, why)
	}
	return value{sentinel}
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
	if _, single := sortOf(v.info.TypeOf(e)); !single {
		v.unsupported(e.Pos(), fmt.Sprintf("a value of type %s cannot be used here", v.info.TypeOf(e)))
	}
	return val[0]
}

// eval evaluates an expression, checking on the way that it cannot panic.
// guard holds the conditions under which the expression is evaluated at all,
// which matters on the right of && and ||.
func (v *fnVerifier) eval(e ast.Expr, st *state, guard []*logic.Term) value {
	defer v.begin()()
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
		return v.variable(e, st, guard)
	case *ast.StarExpr:
		object, ok := pointee(v.info.TypeOf(e.X))
		if !ok {
			break
		}
		start := v.unit.start()
		pointer := v.eval(e.X, st, guard)
		v.checkNil(st, guard, pointer[0], e.Pos())
		return v.readAt(st, guard, start, types.ExprString(e), e.Pos(), func(sink *state, mem memory) value {
			return v.pointedIn(sink, mem, object, pointer)
		})
	case *ast.UnaryExpr:
		return v.unary(e, st, guard)
	case *ast.BinaryExpr:
		return value{v.binaryExpr(e, st, guard)}
	case *ast.IndexExpr:
		return v.indexExpr(e, st, guard)
	case *ast.SliceExpr:
		return v.sliceExpr(e, st, guard)
	case *ast.SelectorExpr:
		if x, ok := e.X.(*ast.Ident); ok && v.isPackageName(x) {
			if variable, isVar := v.info.Uses[e.Sel].(*types.Var); isVar && isError(variable.Type()) {
				return v.errorVariable(variable, e.Pos(), st)
			}
		}
		// The field selection x.f follows a pointer where x is one, which
		// must then not be nil.
		selection := v.info.Selections[e]
		if selection == nil || selection.Kind() != types.FieldVal {
			v.unsupported(e.Pos(), "only fields can be selected; variables of other packages and method values are not supported")
		}
		// A field of a struct that lies in memory is read on its own, as
		// Go reads it, and not as part of the whole struct.
		start := v.unit.start()
		if v.inMemory(e) && !hopsPointer(v.info.TypeOf(e.X), selection.Index()) {
			lv := v.lvalue(e, st, guard)
			return v.readAt(st, guard, start, types.ExprString(e), e.Pos(), func(sink *state, mem memory) value {
				return v.loadIn(lv, sink, mem)
			})
		}
		return v.fields(v.eval(e.X, st, guard), v.info.TypeOf(e.X), selection.Index(), st, guard, e.Sel.Pos(), start, types.ExprString(e))
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
	if !isError(want) && !isSlice(want) && !isPointer && !isMap(want) {
		v.unsupported(e.Pos(), fmt.Sprintf("nil of type %s is not supported", want))
	}
	return zeroValue(want)
}

// settled returns a value fit to be put into memory. Everything in memory is
// taken to be a value of its type, but a value computed on the right of &&
// or || was only checked on condition that it is evaluated at all. Such a
// value is replaced by an unknown one of the type that equals it under that
// condition.
func (v *fnVerifier) settled(st *state, guard []*logic.Term, val value, t types.Type) value {
	if len(guard) == 0 {
		return val
	}
	stored := v.unknown("stored", t, st)
	for i := range stored {
		st.assume(logic.Implies(logic.And(guard...), v.same(stored[i], val[i])))
	}
	return stored
}

// pointed reads the struct a pointer points to.
func (v *fnVerifier) pointed(st *state, t types.Type, pointer value) value {
	return v.pointedIn(st, st.mem, t, pointer)
}

// pointedIn reads the struct a pointer points to in some memory.
func (v *fnVerifier) pointedIn(sink *state, mem memory, t types.Type, pointer value) value {
	val := v.fetch(sink, mem, v.cellsOf(t), pointer[0], pointer[1])
	v.noteTyped(sink, val, t)
	return val
}

// inMemory reports whether an expression is a struct, or a field of one,
// that lies in memory: a variable whose address is taken, what a pointer
// points to, an element of a slice, or a field of one of these.
func (v *fnVerifier) inMemory(e ast.Expr) bool {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		variable, ok := v.info.ObjectOf(e).(*types.Var)
		return ok && v.boxed[variable]
	case *ast.StarExpr:
		_, ok := pointee(v.info.TypeOf(e.X))
		return ok
	case *ast.IndexExpr:
		return isSlice(v.info.TypeOf(e.X))
	case *ast.SelectorExpr:
		selection := v.info.Selections[e]
		if selection == nil || selection.Kind() != types.FieldVal {
			return false
		}
		if _, viaPointer := pointee(v.info.TypeOf(e.X)); viaPointer {
			return true
		}
		return v.inMemory(e.X)
	}
	return false
}

// hopsPointer reports whether a path of field indices from a value of the
// type follows a pointer after its first step, as a field promoted from an
// embedded pointer does.
func hopsPointer(t types.Type, path []int) bool {
	if object, ok := pointee(t); ok {
		t = object
	}
	for _, index := range path[:len(path)-1] {
		field := t.Underlying().(*types.Struct).Field(index).Type()
		if _, ok := pointee(field); ok {
			return true
		}
		t = field
	}
	return false
}

// newObject creates a struct holding the given value in an allocation of its
// own and returns the pointer to it.
func (v *fnVerifier) newObject(st *state, t types.Type, val value) value {
	ref := v.alloc(st, v.pass.TypesSizes.Sizeof(t) > 0)
	v.put(st, v.cellsOf(t), ref, logic.IntLit(0), val)
	v.noteBorn(st, ref, rowKeys(v.cellsOf(t)))
	return value{ref, logic.IntLit(0)}
}

// addressOf evaluates &x for a struct x: a variable, a struct another
// pointer points to, an element of a slice, or a field of one of these. The
// pointer it yields points into the allocation x is part of; a variable
// whose address is taken has one of its own, see findBoxed.
func (v *fnVerifier) addressOf(e ast.Expr, st *state, guard []*logic.Term) value {
	_, isStruct := v.info.TypeOf(e).Underlying().(*types.Struct)
	switch lv := v.place(e); {
	case !isStruct:
		v.unsupported(e.Pos(), fmt.Sprintf("taking the address of %s is not supported: it is a %s, and only pointers to structs are supported",
			types.ExprString(e), v.info.TypeOf(e)))
	case lv.kind != placeMem:
		v.unsupported(e.Pos(), fmt.Sprintf("taking the address of %s is not supported", types.ExprString(e)))
	}
	lv := v.lvalue(e, st, guard)
	return value{lv.ref, logic.Add(lv.at, logic.IntLit(lv.offset))}
}

// unary evaluates a unary operator.
func (v *fnVerifier) unary(e *ast.UnaryExpr, st *state, guard []*logic.Term) value {
	if e.Op == token.AND {
		t := v.info.TypeOf(e.X)
		_, isStruct := t.Underlying().(*types.Struct)
		if lit, ok := ast.Unparen(e.X).(*ast.CompositeLit); ok && isStruct {
			return v.newObject(st, t, v.literal(lit, t, st, guard))
		}
		return v.addressOf(e.X, st, guard)
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
	case token.XOR:
		return value{v.complement(operand, v.info.TypeOf(e), e.Pos())}
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
		case isPointer, isSlice(t), isMap(t):
			isNil = logic.Eq(val[0], logic.RefLit(0))
		default:
			v.unsupported(e.Pos(), fmt.Sprintf("comparing a %s with nil is not supported", t))
		}
		if e.Op == token.NEQ {
			return logic.Not(isNil)
		}
		return isNil
	}
	if (isError(v.info.TypeOf(e.X)) || isError(v.info.TypeOf(e.Y))) && (e.Op == token.EQL || e.Op == token.NEQ) {
		return v.compareErrors(e.X, e.Y, e.Op, st, guard, e.Pos())
	}
	if object, isPointer := pointee(v.info.TypeOf(e.X)); isPointer {
		if v.pass.TypesSizes.Sizeof(object) == 0 {
			v.unsupported(e.Pos(), "pointers to values of size zero may or may not be equal, so comparing them is not supported")
		}
		// Two pointers are equal when both are nil, or when they point to
		// the same position of the same allocation.
		a, b := v.eval(e.X, st, guard), v.eval(e.Y, st, guard)
		same := logic.And(logic.Eq(a[0], b[0]), logic.Or(logic.Eq(a[0], logic.RefLit(0)), logic.Eq(a[1], b[1])))
		switch e.Op {
		case token.EQL:
			return same
		case token.NEQ:
			return logic.Not(same)
		}
		v.unsupported(e.Pos(), fmt.Sprintf("operator %s is not supported for pointers", e.Op))
	}
	if e.Op == token.LAND || e.Op == token.LOR {
		// Go decides after the left operand whether to evaluate the right
		// one, and evaluates it after that decision.
		u := v.unit
		decided := u.pushCeiling()
		left := v.expr(e.X, st, guard)
		u.reach(decided)
		u.event()
		floor := u.floor
		u.floor = u.after
		defer func() { u.floor = floor }()
		if e.Op == token.LAND {
			return logic.And(left, v.expr(e.Y, st, append(slices.Clip(guard), left)))
		}
		return logic.Or(left, v.expr(e.Y, st, append(slices.Clip(guard), logic.Not(left))))
	}
	left := v.expr(e.X, st, guard)
	return v.binary(e.Op, left, v.expr(e.Y, st, guard), v.info.TypeOf(e), e.OpPos, st, guard)
}

// indexExpr evaluates s[i] for a slice or a string.
func (v *fnVerifier) indexExpr(e *ast.IndexExpr, st *state, guard []*logic.Term) value {
	t := v.info.TypeOf(e.X)
	switch {
	case isMap(t) && mapModelled(t):
		// Reading a key that is absent, or any key of a nil map, gives the
		// zero value.
		keyType, _ := mapParts(t)
		start := v.unit.start()
		ref, key := v.expr(e.X, st, guard), v.evalAs(e.Index, keyType, st, guard)[0]
		return v.readAt(st, guard, start, types.ExprString(e), e.Pos(), func(sink *state, mem memory) value {
			return v.mapValue(sink, mem, t, ref, key)
		})
	case isString(t):
		text, index := v.expr(e.X, st, guard), v.expr(e.Index, st, guard)
		v.checkIndex(st, guard, logic.Len(text), index, e.Pos())
		char := logic.Select(text, index)
		st.assume(logic.Implies(logic.And(guard...), v.typeFact(char, v.info.TypeOf(e))))
		return value{char}
	case isSlice(t):
		start := v.unit.start()
		header, index := v.eval(e.X, st, guard), v.expr(e.Index, st, guard)
		v.checkIndex(st, guard, header[2], index, e.Pos())
		if _, ok := layoutOf(elemType(t)); !ok {
			break
		}
		return v.readAt(st, guard, start, types.ExprString(e), e.Pos(), func(sink *state, mem memory) value {
			element, _ := v.element(sink, mem, header, t, index)
			return element
		})
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
	return value{header[0], v.elementAt(header, t, lo), logic.Sub(hi, lo), logic.Sub(limit, lo)}
}

// fields follows a path of field indices from a value. A step through a
// pointer reads memory; start is the number of events before the operand
// was evaluated, and what names the selection.
func (v *fnVerifier) fields(cur value, t types.Type, path []int, st *state, guard []*logic.Term, pos token.Pos, start int, what string) value {
	for _, index := range path {
		from := t
		object, viaPointer := pointee(t)
		if !viaPointer {
			next, fieldType, ok := v.member(st, st.mem, cur, t, index)
			if !ok {
				v.unsupported(pos, fmt.Sprintf("this field has type %s, which is not supported", fieldType))
			}
			cur, t = next, fieldType
			continue
		}
		v.checkNil(st, guard, cur[0], pos)
		field := object.Underlying().(*types.Struct).Field(index).Type()
		if _, _, ok := fieldLeaves(object, index); !ok {
			v.unsupported(pos, fmt.Sprintf("this field has type %s, which is not supported", field))
		}
		pointer := cur
		cur = v.readAt(st, guard, start, what, pos, func(sink *state, mem memory) value {
			next, _, _ := v.member(sink, mem, pointer, from, index)
			return next
		})
		t = field
	}
	return cur
}

// literal evaluates a composite literal: a struct value, a new slice, or,
// where the & is left out inside another literal, a new object.
func (v *fnVerifier) literal(e *ast.CompositeLit, t types.Type, st *state, guard []*logic.Term) value {
	if object, ok := pointee(t); ok {
		return v.newObject(st, object, v.literal(e, object, st, guard))
	}
	if isMap(t) {
		return v.mapLiteral(e, t, st, guard)
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
			copy(val[lo:], v.settled(st, guard, v.evalAs(initial, u.Field(index).Type(), st, guard), u.Field(index).Type()))
		}
		return val
	case *types.Slice:
		if _, ok := layoutOf(u.Elem()); !ok {
			v.unsupported(e.Pos(), fmt.Sprintf("slices of %s are not supported", u.Elem()))
		}
		var elements []value
		for _, element := range e.Elts {
			if _, keyed := element.(*ast.KeyValueExpr); keyed {
				v.unsupported(element.Pos(), "keyed slice literals are not supported")
			}
			elements = append(elements, v.settled(st, guard, v.evalAs(element, u.Elem(), st, guard), u.Elem()))
		}
		length := logic.IntLit(int64(len(e.Elts)))
		return v.allocSlice(st, u.Elem(), elements, length, length)
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
		case isMap(v.info.TypeOf(e.Args[0])) && builtin("len"):
			return v.readAt(st, guard, v.unit.start(), types.ExprString(e), e.Pos(), func(sink *state, mem memory) value {
				return value{v.mapLen(sink, mem, v.info.TypeOf(e.Args[0]), operand[0])}
			})
		case isMap(v.info.TypeOf(e.Args[0])):
			v.unsupported(e.Pos(), "cap of a map is not supported")
		case isString(v.info.TypeOf(e.Args[0])):
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
		// new takes a type, or a value to start from.
		initial := zeroValue(t)
		if !v.info.Types[e.Args[0]].IsType() {
			initial = v.settled(st, guard, v.eval(e.Args[0], st, guard), t)
		}
		return v.newObject(st, t, initial)
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
	if isMap(t) && mapModelled(t) {
		// A size is only a hint, but it is evaluated.
		for _, hint := range e.Args[1:] {
			v.check(st, guard, logic.Le(logic.IntLit(0), v.expr(hint, st, guard)), hint.Pos(), "make size may be negative")
		}
		return v.newMap(st, t)
	}
	if !isSlice(t) || len(e.Args) < 2 {
		v.unsupported(e.Pos(), "make is only supported for slices with a length")
	}
	if _, ok := layoutOf(elemType(t)); !ok {
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
	v.checkAlloc(st, guard, capacity, elemType(t), e.Pos(), "the slice made")
	return v.allocSlice(st, elemType(t), nil, length, capacity)
}

// sameValue reports whether Go converts between two types without changing
// the value: the types are made the same way, struct tags aside, or are
// pointers to structs that are. What such a value refers to stays where it
// is, in the same regions of memory, since those do not depend on the names
// of types or on tags.
func sameValue(from, to types.Type) bool {
	a, fromPointer := from.Underlying().(*types.Pointer)
	b, toPointer := to.Underlying().(*types.Pointer)
	if fromPointer && toPointer {
		return types.IdenticalIgnoreTags(a.Elem().Underlying(), b.Elem().Underlying())
	}
	return types.IdenticalIgnoreTags(from.Underlying(), to.Underlying())
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
		start := v.unit.start()
		header := v.eval(e.Args[0], st, guard)
		return v.readAt(st, guard, start, "the elements of "+types.ExprString(e.Args[0]), e.Pos(), func(sink *state, mem memory) value {
			text, _ := v.view(sink, mem, header, from)
			return value{text}
		})
	case isString(from) && bytes(to):
		// Go does not say how much capacity the new array has. The bytes go
		// into memory and the new slice is described by facts that hold
		// unconditionally, so on the right of && or || the string is first
		// replaced by one that is a string whether or not it is evaluated.
		text := v.settled(st, guard, value{v.expr(e.Args[0], st, guard)}, from)[0]
		only := v.cellsOf(elemType(to))[0]
		copied := value{v.alloc(st, true), logic.IntLit(0), logic.Len(text), v.fresh("cap", logic.Int)}
		st.storeRow(only.key, only.sort, copied[0], text)
		v.noteBorn(st, copied[0], rowKeys([]cell{only}))
		st.assume(v.wellFormed(copied, to, st.brk))
		return copied
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
	// A conversion that leaves the value as it is must also leave it in
	// the same memory, which pointers and slices of differently named
	// types would not be.
	if sameValue(from, to) {
		return val
	}
	v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to a %s is not supported", from, to))
	return nil
}
