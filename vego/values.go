package vego

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"

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

// exprAs evaluates an expression that is assigned to something of type want.
// It differs from expr only for nil, which has no type of its own.
func (v *fnVerifier) exprAs(e ast.Expr, want types.Type, st *state, guard []*logic.Term) *logic.Term {
	if !v.isNil(e) {
		return v.expr(e, st, guard)
	}
	sort, ok := sortOf(want)
	if !ok || (sort != logic.Err && !isSlice(want)) {
		v.unsupported(e.Pos(), fmt.Sprintf("nil of type %s is not supported", want))
	}
	return zero(sort)
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

// text evaluates the string forms that have no slice counterpart:
// concatenation, substrings, and conversions to and from []byte.
func (v *fnVerifier) text(e ast.Expr, st *state) *logic.Term {
	switch e := ast.Unparen(e).(type) {
	case *ast.BinaryExpr:
		left := v.expr(e.X, st, nil)
		return v.binary(e.Op, left, v.expr(e.Y, st, nil), v.info.TypeOf(e), e.OpPos, st, nil)
	case *ast.SliceExpr:
		if !isString(v.info.TypeOf(e.X)) || e.Slice3 {
			break
		}
		whole := v.expr(e.X, st, nil)
		lo, hi := logic.IntLit(0), logic.Len(whole)
		if e.Low != nil {
			lo = v.expr(e.Low, st, nil)
		}
		if e.High != nil {
			hi = v.expr(e.High, st, nil)
		}
		within := logic.And(logic.Le(logic.IntLit(0), lo), logic.Le(lo, hi), logic.Le(hi, logic.Len(whole)))
		v.check(st, nil, within, e.Pos(), "substring bounds may be out of range")
		return logic.Subseq(whole, lo, hi)
	case *ast.CallExpr:
		if !v.info.Types[e.Fun].IsType() {
			break
		}
		// string(b) and []byte(s) copy, so the result is the same sequence
		// of bytes and shares nothing with the operand.
		from, to := v.info.TypeOf(e.Args[0]), v.info.TypeOf(e)
		bytes := func(t types.Type) bool {
			return isString(t) || (isSlice(t) && types.Identical(t.Underlying().(*types.Slice).Elem().Underlying(), types.Typ[types.Uint8]))
		}
		if bytes(from) && bytes(to) && (isString(from) || isString(to)) {
			return v.expr(e.Args[0], st, nil)
		}
	}
	return nil
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
// Formatting calls the String, Error, and Format methods of its operands,
// which is code the verifier does not see. An argument of a type with methods
// is therefore rejected, except an error, whose methods cannot reach the
// slices of this function under the rule that unverified code keeps none.
func (v *fnVerifier) newError(call *ast.CallExpr, st *state, guard []*logic.Term) *logic.Term {
	for _, arg := range call.Args {
		t := v.info.TypeOf(arg)
		if sort, ok := sortOf(t); (!ok || sort != logic.Err) && types.NewMethodSet(t).Len() > 0 {
			v.unsupported(arg.Pos(), fmt.Sprintf(
				"formatting a value of type %s would call its methods, which are not verified", t))
		}
		v.expr(arg, st, guard)
	}
	created := v.fresh("error", logic.Err)
	st.assume(logic.Not(logic.IsNil(created)))
	return created
}
