package vego

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Formatting runs code. Package fmt calls the Format, GoString, Error, and
// String methods of what it is given, and of what that holds, so a value
// passed to fmt.Println is code handed over as much as an error passed to
// a trusted function is. One rule decides what may be formatted, for
// fmt.Errorf, which is built in, and for every trusted function whose entry
// lists the parameter under formats: the values of fmt and log, and a
// project's own logging functions.
//
// A value may be formatted when formatting it runs no code: its type and
// everything inside it is plain (see plainReason), or it is an error of
// known origin, whose methods are those of the standard library or vouched
// for.

// fmtMethods are the methods package fmt calls on what it formats.
var fmtMethods = []string{"Format", "GoString", "Error", "String"}

// readFormats reads what the entry of a trusted function lists under
// formats: one parameter of type any or ...any, whose values the function
// formats, and at most one string parameter, its format.
//
// The claim is that the function formats those values as package fmt does
// and does nothing else with them: it runs only the methods of them that
// fmt runs, while the call lasts and on the goroutine that called it, keeps
// none of them, and builds nothing longer than fmt would print. vego checks
// at each call that formatting the values runs no code that is not plain,
// in the state of the call. That state is the state in which formatting
// runs only if nothing the function does before it changes memory a caller
// can see, so formats goes with modifies: [] and without calls, and runs
// may list only values whose contracts write nothing.
func (pv *pkgVerifier) readFormats(fn *funcInfo, entry *trustEntry) {
	if len(entry.formats) == 0 {
		return
	}
	sig := fn.obj.Type().(*types.Signature)
	for _, item := range entry.formats {
		param, ok := fn.paramNames[item.text]
		switch {
		case !ok || param == sig.Recv():
			fn.defect("its formats %q: %s is not a parameter", item.text, item.text)
		case fn.runs[param]:
			fn.defect("its formats lists %s, which its runs lists too; a parameter is either formatted or run", item.text)
		case isString(param.Type()) && types.Identical(param.Type(), types.Typ[types.String]):
			if fn.format != nil {
				fn.defect("its formats lists two strings, %s and %s; it can list one, the format", fn.format.Name(), item.text)
			}
			fn.format = param
		case isAnyParam(sig, param):
			if fn.formatted != nil {
				fn.defect("its formats lists %s and %s; it can list one parameter of type any or ...any", fn.formatted.Name(), item.text)
			}
			fn.formatted = param
		default:
			fn.defect("its formats lists %s, of type %s; it can list a string, the format, and a parameter of type any or ...any", item.text, param.Type())
		}
	}
	if fn.formatted == nil {
		fn.defect("its formats lists no parameter of type any or ...any whose values it formats")
	}
	if len(entry.modifies) > 0 {
		fn.defect("it lists formats and writes memory under modifies; the values are checked in the state of the call, " +
			"which is the state in which they are formatted only if the function writes nothing a caller can see")
	}
	if len(entry.calls) > 0 {
		fn.defect("it lists formats and has calls; the values are checked in the state of the call, " +
			"which a function it calls before it formats them could change")
	}
	for param := range fn.runs {
		if what := pv.writingCode(param.Type(), map[types.Type]bool{}); what != "" {
			fn.defect("it lists formats and runs %s, which can hold %s; the values are checked in the state of the call, "+
				"which that code could change before they are formatted", param.Name(), what)
		}
	}
}

// isAnyParam reports whether a parameter has type any, or is the variadic
// parameter ...any.
func isAnyParam(sig *types.Signature, param *types.Var) bool {
	t := param.Type()
	if sig.Variadic() && param == sig.Params().At(sig.Params().Len()-1) {
		t = elemType(t)
	}
	iface, ok := types.Unalias(t).(*types.Interface)
	return ok && iface.Empty()
}

// writingCode names what a value of a type can hold that a trusted function
// may run and whose contract writes memory: a function value or an
// interface value whose type's contract lists something under Modifies. It
// returns "" when there is none.
func (pv *pkgVerifier) writingCode(t types.Type, seen map[types.Type]bool) string {
	if t == nil || seen[t] {
		return ""
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Signature:
		if fn := pv.valueContract(t); fn != nil && len(fn.modifies) > 0 {
			return "a function value of type " + t.String() + ", whose contract modifies memory"
		}
	case *types.Interface:
		for method := range u.Methods() {
			if fn := pv.methodContract(method); fn != nil && len(fn.modifies) > 0 {
				return "an interface value whose method " + methodTitle(method) + " modifies memory"
			}
		}
	case *types.Pointer:
		return pv.writingCode(u.Elem(), seen)
	case *types.Slice:
		return pv.writingCode(u.Elem(), seen)
	case *types.Array:
		return pv.writingCode(u.Elem(), seen)
	case *types.Map:
		if what := pv.writingCode(u.Key(), seen); what != "" {
			return what
		}
		return pv.writingCode(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if what := pv.writingCode(field.Type(), seen); what != "" {
				return what
			}
		}
	}
	return ""
}

// plainReason says why formatting a value of a type may run code, follow
// pointers, or not end, or returns "" when it cannot: the type has none of
// the methods fmt calls, and it is a basic type, a slice of plain
// elements, or a struct of plain fields. fmt prints such a value element
// by element and field by field and calls nothing. Only the value's own
// method set counts: fmt reaches what it formats through an interface,
// where nothing is addressable, so methods of a pointer to it are never
// called.
//
// A type that holds itself, as type Nest []Nest or a struct with a slice
// of itself, is not plain: such a slice can hold itself, n[0] = n, and fmt
// would then follow it until the stack runs out. visiting holds the types
// on the way to t, and a type met twice on one way is such a cycle.
func plainReason(t types.Type, visiting map[types.Type]bool) string {
	if visiting[t] {
		return fmt.Sprintf("%s holds itself, so a value of it can hold itself, which fmt would follow without end", t)
	}
	visiting[t] = true
	defer delete(visiting, t)
	methods := types.NewMethodSet(t)
	for _, name := range fmtMethods {
		for method := range methods.Methods() {
			if method.Obj().Name() == name {
				return fmt.Sprintf("%s has a method %s, which fmt would call", t, name)
			}
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return fmt.Sprintf("%s is a pointer, which fmt would follow", t)
		}
		return ""
	case *types.Slice:
		return plainReason(u.Elem(), visiting)
	case *types.Struct:
		for field := range u.Fields() {
			if why := plainReason(field.Type(), visiting); why != "" {
				return why
			}
		}
		return ""
	case *types.Pointer:
		return fmt.Sprintf("%s is a pointer, which fmt would follow", t)
	case *types.Interface:
		return fmt.Sprintf("%s is an interface, which can hold a value with methods that fmt would call", t)
	}
	return fmt.Sprintf("%s cannot be formatted by verified code", t)
}

// checkFormattable refuses a value that the function named by who formats,
// when formatting it may run code nobody has checked.
func (v *fnVerifier) checkFormattable(arg ast.Expr, who string) {
	t := v.info.TypeOf(arg)
	if isError(t) {
		// Formatting an error runs its methods, which known origin of
		// either kind makes harmless.
		if !v.knownError(v.bodyOrigins(), arg, -1, map[*types.Var]bool{}) {
			v.unsupported(arg.Pos(), fmt.Sprintf("formatting %s would run the methods of an error whose origin is not known; "+
				"only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a trusted contract vouches for, "+
				"can be formatted%s", types.ExprString(arg), v.originWhy(arg)))
		}
		return
	}
	if why := plainReason(t, map[types.Type]bool{}); why != "" {
		v.unsupported(arg.Pos(), fmt.Sprintf("%s formats %s, a value of type %s, and that may run code nobody has checked: %s; "+
			"only numbers, booleans, strings, and slices and structs of them without such methods, and errors of known origin, can be formatted",
			who, types.ExprString(arg), t, why))
	}
}

// checkFormatted checks what a call gives the parameter that a trusted
// function formats: a value passed as any, or each argument of a pack, is
// checked on its own, and a slice passed with ... is refused, since what its
// elements hold is not known.
func (v *fnVerifier) checkFormatted(call *ast.CallExpr, fn *funcInfo) {
	if fn.formatted == nil {
		return
	}
	for _, passed := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		switch {
		case passed.param != fn.formatted:
		case passed.spread:
			v.unsupported(passed.expr.Pos(), fmt.Sprintf("%s formats what the slice %s holds, which can be anything; "+
				"list the values in the call instead, so that each is checked", fn.obj.Name(), types.ExprString(passed.expr)))
		case passed.packed:
			for _, arg := range passed.pack {
				v.checkFormattable(arg, fn.obj.Name())
			}
		default:
			v.checkFormattable(passed.expr, fn.obj.Name())
		}
	}
}

// fmtSlack is what a function that formats may build beyond what fmt
// prints: a logger's header and newline, or a prefix that a logging
// function of a project adds. What a logger's prefix and the name of a
// file take beyond it is assumed.
const fmtSlack = 4096

// checkFormatAlloc proves that what a function builds from what it formats
// can be allocated: twice what fmtBound counts, plus fmtSlack, plus a page,
// since the buffer fmt writes into grows by append (see appendTo). format
// is the expression of the format, or nil, with its value; operands are the
// values formatted, as they were before they were converted to any. It
// returns the bound on what fmt writes when that bound counts all of it,
// and nil otherwise.
func (v *fnVerifier) checkFormatAlloc(st *state, guard []*logic.Term, call *ast.CallExpr, who string, format ast.Expr, formatVal value, operands []fmtOperand) *logic.Term {
	spec := fmtSpec{line: true}
	if format != nil {
		if tv := v.info.Types[format]; tv.Value != nil && tv.Value.Kind() == constant.String {
			spec = constantSpec(constant.StringVal(tv.Value))
		} else {
			length := logic.Len(formatVal[0])
			spec = fmtSpec{verbs: length, length: length, width: fmtMaxWidth, precision: fmtMaxWidth, expands: true}
		}
	}
	bound, complete := fmtBound(spec, operands)
	built := logic.Add(bound, logic.IntLit(fmtSlack))
	room := logic.Add(logic.Mul(built, logic.IntLit(2)), logic.IntLit(1<<16))
	v.check(st, guard, logic.Le(room, logic.BigLit(v.maxAlloc())), call.Pos(),
		"what %s builds from what it formats may be more than can be allocated; bound the lengths of the strings and slices it formats, "+
			"and of a format that is not a constant", who)
	if !complete {
		return nil
	}
	return bound
}

// formatted returns an operand of formatting, with the value an expression
// had as it was converted, or nil for an expression that held one.
func (v *fnVerifier) formatted(e ast.Expr, held value) fmtOperand {
	if held == nil || v.isNil(e) {
		// nil, which formats as <nil> or %!d(<nil>).
		return fmtOperand{t: types.Typ[types.UntypedNil]}
	}
	return fmtOperand{val: held, t: v.info.TypeOf(e)}
}

// checkFormattedAlloc is checkFormatAlloc for a call of a trusted function
// whose entry lists formats, once its arguments have been evaluated.
func (v *fnVerifier) checkFormattedAlloc(st *state, guard []*logic.Term, call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value) *logic.Term {
	if fn.formatted == nil {
		return nil
	}
	var format ast.Expr
	var operands []fmtOperand
	for _, passed := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		switch {
		case passed.param == fn.format:
			format = passed.expr
		case passed.param == fn.formatted && passed.packed:
			for _, e := range passed.pack {
				operands = append(operands, v.formatted(e, v.held[ast.Unparen(e)]))
			}
		case passed.param == fn.formatted:
			operands = append(operands, v.formatted(passed.expr, v.held[ast.Unparen(passed.expr)]))
		}
	}
	var formatVal value
	if fn.format != nil {
		formatVal = args[fn.format]
	}
	return v.checkFormatAlloc(st, guard, call, fn.obj.Name(), format, formatVal, operands)
}

// returnsFormatted reports whether a function is one of those of fmt
// documented to return the string they format: Sprintf, Sprint, and
// Sprintln.
func returnsFormatted(callee *types.Func) bool {
	if callee.Pkg() == nil || callee.Pkg().Path() != "fmt" {
		return false
	}
	switch callee.Name() {
	case "Sprintf", "Sprint", "Sprintln":
		return true
	}
	return false
}
