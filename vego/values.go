package vego

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math/big"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// isSlice reports whether a type is a slice. Strings are modelled as
// sequences too, but only slices can be written through, so only they are
// subject to the rules about sharing a backing array.
func isSlice(t types.Type) bool {
	if t == nil {
		return false
	}
	_, ok := t.Underlying().(*types.Slice)
	return ok
}

// isFunc reports whether a type is a function type that is modelled: one
// without type parameters. A function value is one leaf, a reference that
// is zero exactly when the value is nil. Go lets a function value be
// compared with nil and nothing else, so nothing else is known of it.
func isFunc(t types.Type) bool {
	if t == nil {
		return false
	}
	sig, ok := t.Underlying().(*types.Signature)
	return ok && sig.TypeParams() == nil && sig.RecvTypeParams() == nil
}

// isIface reports whether a type is an interface type other than error that
// is modelled: a set of methods, not a constraint, without type parameters
// or type arguments, and not one that holds the methods of error, whose
// values would be errors that the model of errors does not describe. A
// value of such a type is one leaf, a reference that is zero exactly when
// the value is the nil interface. Converting a concrete value gives a
// reference that is not zero, even for a nil pointer, as in Go; converting
// one interface value to another keeps the reference.
func isIface(t types.Type) bool {
	if t == nil || isError(t) {
		return false
	}
	u, ok := t.Underlying().(*types.Interface)
	if !ok || !u.IsMethodSet() {
		return false
	}
	if named, isNamed := types.Unalias(t).(*types.Named); isNamed && (named.TypeParams() != nil || named.TypeArgs() != nil) {
		return false
	}
	if embedsDeclared(t) {
		return false
	}
	errorMethod := types.Universe.Lookup("error").Type().Underlying().(*types.Interface).Method(0)
	for method := range u.Methods() {
		if method == errorMethod {
			return false
		}
	}
	return true
}

// embedsDeclared reports whether a type is an interface type without a name
// that has a method of a defined interface type, which it embeds. Two such
// types are identical when their methods have the same names and
// signatures, whichever declarations they come from, and Go converts
// nothing between identical types. So a value of interface{ A } would pass
// as an interface{ B } without a conversion that could check it against
// the contracts of B. A defined type is identical only to itself.
func embedsDeclared(t types.Type) bool {
	if _, named := types.Unalias(t).(*types.Named); named {
		return false
	}
	u, ok := t.Underlying().(*types.Interface)
	if !ok {
		return false
	}
	for method := range u.Methods() {
		if recv := method.Type().(*types.Signature).Recv(); recv != nil {
			if _, declared := types.Unalias(recv.Type()).(*types.Named); declared {
				return true
			}
		}
	}
	return false
}

// unsupportedHint says why an interface literal that embeds a declared
// interface is not supported, and what to do instead. It returns "" for any
// other type.
func unsupportedHint(t types.Type) string {
	if hint := arrayHint(t); hint != "" {
		return hint
	}
	if path, holder, array := arrayField(t, map[types.Type]bool{}); path == "itself" {
		return fmt.Sprintf("; %s is an array, and arrays are not supported yet", holder)
	} else if path != "" {
		return fmt.Sprintf("; %s holds an array of %s in %s, and arrays in structs are supported only for elements of one byte yet", holder, array.Underlying().(*types.Array).Elem(), path)
	}
	if !embedsDeclared(t) {
		return ""
	}
	return "; an interface literal that embeds a declared interface is the same type as any other with methods of " +
		"the same names and signatures, whose contracts may differ, so declare a defined interface type, as in type D interface{ A }, and use it here"
}

// arrayHint says why an array type, or a pointer to one, is not supported,
// and what to write instead, or returns "".
func arrayHint(t types.Type) string {
	switch u := t.Underlying().(type) {
	case *types.Pointer:
		if isArray(u.Elem()) {
			return fmt.Sprintf("; %s points to an array, and pointers to arrays are not supported yet; use a slice of the array, as in a[:]", t)
		}
	case *types.Array:
		if _, plain := plainElem(u.Elem()); !plain && u.Len() != 0 {
			instead := ""
			switch elem := u.Elem(); {
			case isArray(elem):
				// A slice of arrays cannot be indexed either.
				instead = fmt.Sprintf("; use one array of %d elements indexed i*%d + j, or a slice of slices, instead", u.Len()*arrayLen(elem), arrayLen(elem))
			case readableElem(elem):
				instead = fmt.Sprintf("; use a slice of %s instead", elem)
			}
			return fmt.Sprintf("; %s is an array of %s, and only arrays of numbers and booleans are supported yet%s", t, u.Elem(), instead)
		}
	}
	return ""
}

// readableElem reports whether the elements of a slice of the type can be
// read: the type is modelled as an element, and a pointer in it points to
// a struct.
func readableElem(t types.Type) bool {
	if _, ok := elemLayout(t); !ok {
		return false
	}
	if _, isPointer := t.Underlying().(*types.Pointer); isPointer {
		_, ok := pointee(t)
		return ok
	}
	return true
}

// arrayField returns the field at any depth through which a type holds an
// array that a struct cannot hold, as field out or field e.buf, with the
// type that holds it and the type of the array, or "" for a type that holds
// none where a value of it lies: in itself, in what a pointer points to, or
// in the elements of a slice.
func arrayField(t types.Type, seen map[types.Type]bool) (path string, holder, array types.Type) {
	if seen[t] {
		return "", nil, nil
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Pointer:
		return arrayField(u.Elem(), seen)
	case *types.Slice:
		return arrayField(u.Elem(), seen)
	case *types.Array:
		if u.Len() != 0 {
			return "itself", t, t
		}
	case *types.Struct:
		for field := range u.Fields() {
			if field.Name() == "_" {
				continue
			}
			if _, isArray := field.Type().Underlying().(*types.Array); isArray && holdsArray(field.Type()) {
				return "field " + field.Name(), t, field.Type()
			}
			if inner, _, array := arrayField(field.Type(), seen); inner != "" && holdsArray(field.Type()) {
				return "field " + field.Name() + "." + strings.TrimPrefix(inner, "field "), t, array
			}
		}
	}
	return "", nil, nil
}

// holdsCodeRef reports whether a type is one whose values are a single
// reference that tells only whether the value is nil: a function type or
// an interface type other than error.
func holdsCodeRef(t types.Type) bool {
	return isFunc(t) || isIface(t)
}

func isString(t types.Type) bool {
	basic, ok := t.Underlying().(*types.Basic)
	return ok && basic.Info()&types.IsString != 0
}

// isBool reports whether a type is a boolean type.
func isBool(t types.Type) bool {
	basic, ok := t.Underlying().(*types.Basic)
	return ok && basic.Info()&types.IsBoolean != 0
}

// isNil reports whether an expression is the predeclared nil.
func (v *fnVerifier) isNil(e ast.Expr) bool {
	return v.info.Types[ast.Unparen(e)].IsNil()
}

// maxLiteral is the longest string constant whose bytes are modelled; longer
// ones are only known by their length.
const maxLiteral = 512

// constant converts a compile-time constant to a term of the given sort.
// Floats are opaque, so a float constant is only a name for its value.
func (v *fnVerifier) constant(value constant.Value, sort logic.Sort, e ast.Expr, st *state) *logic.Term {
	switch sort {
	case logic.Int:
		if literal, ok := literalOf(constant.ToInt(value)); ok {
			return literal
		}
	case logic.Bool:
		if literal, ok := literalOf(value); ok {
			return literal
		}
	case logic.Float:
		return logic.Const("float "+value.ExactString(), logic.Float)
	case logic.IntSeq:
		if value.Kind() != constant.String {
			break
		}
		text := constant.StringVal(value)
		if len(text) <= maxLiteral {
			return logic.Bytes(text)
		}
		long := v.fresh("literal", logic.IntSeq)
		st.assume(logic.Eq(logic.Len(long), logic.IntLit(int64(len(text)))))
		return long
	}
	v.unsupported(e.Pos(), "this constant is not supported")
	return nil
}

// opaque evaluates an operator whose result the logic knows nothing about:
// arithmetic and comparison of floats, and ordering of strings. The operands have already been evaluated, so any panic inside
// them is accounted for; the result is an arbitrary value of the right sort.
func (v *fnVerifier) opaque(op token.Token, operand *logic.Term) *logic.Term {
	switch op {
	case token.EQL, token.NEQ, token.LSS, token.LEQ, token.GTR, token.GEQ:
		return v.fresh("unknown", logic.Bool)
	}
	return v.fresh("unknown", operand.Sort)
}

// substring evaluates s[i:j] on a string. Unlike a slice of a slice it
// shares nothing that could be written, so it is simply a shorter sequence.
func (v *fnVerifier) substring(e *ast.SliceExpr, st *state, guard []*logic.Term) *logic.Term {
	if e.Slice3 {
		v.unsupported(e.Pos(), "a string cannot be sliced with a capacity")
	}
	whole := v.expr(e.X, st, guard)
	// The length is named, so that the substring holds the string once.
	length := v.named(st, "len", logic.Len(whole))
	lo, hi := logic.IntLit(0), length
	if e.Low != nil {
		lo = v.expr(e.Low, st, guard)
	}
	if e.High != nil {
		hi = v.expr(e.High, st, guard)
	}
	within := logic.And(logic.Le(logic.IntLit(0), lo), logic.Le(lo, hi), logic.Le(hi, length))
	v.check(st, guard, within, e.Pos(), "substring bounds may be out of range")
	return logic.Subseq(whole, lo, hi)
}

// errorConstructor recognises errors.New and fmt.Errorf, which always return
// a non-nil error.
func errorConstructor(callee *types.Func) bool {
	if callee == nil || callee.Pkg() == nil {
		return false
	}
	name := callee.Pkg().Path() + "." + callee.Name()
	return name == "errors.New" || name == "fmt.Errorf"
}

// newError evaluates a call to an error constructor: its arguments are
// evaluated for the checks they carry, and the result is some non-nil error.
//
// Formatting calls the String, Error, and Format methods of its operands and
// of what they contain, which is code the verifier does not see. Only values
// that are formatted without such calls are therefore accepted, and errors
// whose origin is known; see knownError.
func (v *fnVerifier) newError(call *ast.CallExpr, st *state, guard []*logic.Term) *logic.Term {
	values := map[ast.Expr]value{}
	callee := typeutil.StaticCallee(v.info, call)
	errorf := callee.Name() == "Errorf"
	var runs []fmtRun
	for _, arg := range call.Args {
		if run := v.checkFormattable(arg, callee.Pkg().Name()+"."+callee.Name(), errorf); run != nil {
			runs = append(runs, fmtRun{call: run, arg: arg})
		}
		// Go converts the arguments of fmt.Errorf after the format to
		// any. That makes no interface value that verified code can call;
		// what formatting may run is decided above.
		if len(v.findConversions().converted[ast.Unparen(arg)]) > 0 {
			values[arg] = v.evalConverted(arg, types.Universe.Lookup("any").Type(), st, guard)
			continue
		}
		values[arg] = v.eval(arg, st, guard)
	}
	if position := v.pass.Fset.Position(call.Pos()); !slices.Contains(v.usage.Constructors, position) {
		v.usage.Constructors = append(v.usage.Constructors, position)
	}
	// The text of an error can be printed on a line of its own, which What
	// a proof assumes says of every error; errors.New stores the text it is
	// given, whose length the logic has a term for, so it is required
	// here (F28).
	// A constant text is short enough whatever the platform, and asks
	// nothing of Z3.
	if tv := v.info.Types[call.Args[0]]; !errorf && len(call.Args) == 1 && (tv.Value == nil || tv.Value.Kind() != constant.String || len(constant.StringVal(tv.Value)) > 1<<20) {
		goal := errorTextFits(v, values[call.Args[0]][0])
		done := v.at(call.Pos())
		result, declared := v.sizedAttempt(st, guard, goal, call.Pos())
		done()
		if result != solver.Proved {
			room := new(big.Int).Sub(v.maxAlloc(), big.NewInt(1<<16))
			room.Rsh(room, 1).Sub(room, big.NewInt(fmtSlack))
			v.report(call.Pos(), "precondition of errors.New may not hold: 2 * (|text| + 4096) + 65536 <= MaxAlloc, so that the text of the error can be printed; "+
				"it holds when |%s| <= %s%s%s", types.ExprString(call.Args[0]), room, v.sizeNote(st, guard, goal), limitNote(result))
		}
		// A goal that only the declared memory proved is not assumed.
		if !declared {
			st.assume(logic.Implies(logic.And(guard...), goal))
		}
	}
	if errorf {
		for i := range runs {
			runs[i].val, runs[i].who = values[runs[i].arg], "fmt.Errorf"
		}
		v.checkFormatRuns(call, runs, st, guard)
		var operands []fmtOperand
		for _, arg := range call.Args[1:] {
			operands = append(operands, v.formatted(st, arg, values[arg]))
		}
		_ = v.checkFormatAlloc(st, guard, call, "fmt.Errorf", fmtSlack, call.Args[0], values[call.Args[0]], operands)
	}
	created := v.fresh("error", logic.Err)
	if made := v.madeErrorType(call, errorf); made != "" {
		if v.madeTypes == nil {
			v.madeTypes = map[string]string{}
		}
		v.madeTypes[created.Name] = made
	}
	v.noteError(st, created)
	// It differs from every opaque variable; see noteOpaque.
	v.madeHere = append(v.madeHere, created)
	for _, value := range v.opaqueErrors {
		v.fact(st, logic.Not(logic.Eq(created, value)))
	}
	switch tree, wrapped := v.callWraps(call); tree {
	case wrapsNothing:
		v.noteTree(st, errorTree{err: created})
	case wrapsOperand:
		wraps := values[wrapped][0]
		if t := v.concreteErrorType(wrapped, -1); t != nil {
			// What %w wraps is the error that holds the value (F33).
			wraps = v.typedError(wrapped, t, values[wrapped], st, guard)
		}
		v.noteTree(st, errorTree{err: created, wraps: wraps})
	}
	return created
}
