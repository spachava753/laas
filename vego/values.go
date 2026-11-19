package vego

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
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

func isString(t types.Type) bool {
	basic, ok := t.Underlying().(*types.Basic)
	return ok && basic.Info()&types.IsString != 0
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
	lo, hi := logic.IntLit(0), logic.Len(whole)
	if e.Low != nil {
		lo = v.expr(e.Low, st, guard)
	}
	if e.High != nil {
		hi = v.expr(e.High, st, guard)
	}
	within := logic.And(logic.Le(logic.IntLit(0), lo), logic.Le(lo, hi), logic.Le(hi, logic.Len(whole)))
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

// formatsPlainly reports whether formatting a value of the type runs no
// code but the formatter's own: a number, boolean, or string without methods,
// or a slice of such values.
func formatsPlainly(t types.Type) bool {
	// A slice type can be its own element type, as in type S []S; following
	// it would never end, and it holds no number, boolean, or string.
	seen := map[types.Type]bool{}
	for isSlice(t) && types.NewMethodSet(t).Len() == 0 {
		if seen[t] {
			return false
		}
		seen[t] = true
		t = elemType(t)
	}
	_, basic := t.Underlying().(*types.Basic)
	return basic && types.NewMethodSet(t).Len() == 0
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
	for _, arg := range call.Args {
		t := v.info.TypeOf(arg)
		switch {
		case isError(t) && !v.knownError(v.originsOf(v.fn.decl.Body), arg, -1, map[*types.Var]bool{}):
			v.unsupported(arg.Pos(), fmt.Sprintf("formatting %s would run the methods of an error whose origin is not known; "+
				"only an error made by errors.New or fmt.Errorf, here or in a verified function, can be formatted%s", types.ExprString(arg), v.originWhy(arg)))
		case !isError(t) && !formatsPlainly(t):
			v.unsupported(arg.Pos(), fmt.Sprintf(
				"formatting a value of type %s may call methods, which are not verified, or follow pointers", t))
		}
		values[arg] = v.eval(arg, st, guard)
	}
	if position := v.pass.Fset.Position(call.Pos()); !slices.Contains(v.usage.Constructors, position) {
		v.usage.Constructors = append(v.usage.Constructors, position)
	}
	created := v.fresh("error", logic.Err)
	v.noteError(st, created)
	switch tree, wrapped := v.callWraps(call); tree {
	case wrapsNothing:
		v.noteTree(st, errorTree{err: created})
	case wrapsOperand:
		v.noteTree(st, errorTree{err: created, wraps: values[wrapped][0]})
	}
	return created
}
