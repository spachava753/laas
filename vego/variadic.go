package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A call of a variadic function gives its last parameter, of type []T, one
// of two things. Written with ..., as in f(xs...), it is the slice itself,
// so the callee may write the caller's array and everything known about
// slice parameters that share memory applies. Written without, as in
// f(a, b), Go makes a new slice of the arguments, with length and capacity
// their number and a new array, or passes nil when there are none. Each
// argument is then converted to T, which is a conversion site like any
// other when T is an interface.

// passedArg is what a call gives one parameter of its callee.
type passedArg struct {
	param *types.Var
	// expr is the argument written for the parameter, followed by ... when
	// spread is set. It is nil for a pack.
	expr   ast.Expr
	spread bool
	// packed is set for the variadic parameter of a call written without
	// ..., and pack holds the arguments that go into its new slice.
	packed bool
	pack   []ast.Expr
}

// bindArgs pairs the arguments of a call with the parameters of its callee,
// given in order without the receiver. It reports false for a call whose
// arguments are the results of a single call, as in g(f()), whose values
// have no expressions of their own.
func bindArgs(info *types.Info, call *ast.CallExpr, params []*types.Var, variadic bool) ([]passedArg, bool) {
	if len(call.Args) == 1 {
		if _, several := info.TypeOf(call.Args[0]).(*types.Tuple); several {
			return nil, false
		}
	}
	fixed := len(params)
	if variadic {
		fixed--
	}
	if len(call.Args) < fixed || (!variadic && len(call.Args) != fixed) {
		return nil, false
	}
	bound := make([]passedArg, 0, len(params))
	for i := range fixed {
		bound = append(bound, passedArg{param: params[i], expr: call.Args[i]})
	}
	if !variadic {
		return bound, true
	}
	last := params[fixed]
	if call.Ellipsis.IsValid() {
		if len(call.Args) != len(params) {
			return nil, false
		}
		return append(bound, passedArg{param: last, expr: call.Args[fixed], spread: true}), true
	}
	return append(bound, passedArg{param: last, packed: true, pack: call.Args[fixed:]}), true
}

// paramsOf lists the parameters of a signature, without the receiver.
func paramsOf(sig *types.Signature) []*types.Var {
	params := make([]*types.Var, sig.Params().Len())
	for i := range params {
		params[i] = sig.Params().At(i)
	}
	return params
}

// bindCall is bindArgs for a callee of the given signature, and stops the
// verification of a call it cannot pair.
func (v *fnVerifier) bindCall(call *ast.CallExpr, sig *types.Signature) []passedArg {
	bound, ok := bindArgs(v.info, call, paramsOf(sig), sig.Variadic())
	if !ok {
		v.unsupported(call.Pos(), "a call with several results as the arguments of another call is not supported yet")
	}
	return bound
}

// text spells what a call gives a parameter, for messages. A spread is
// named by the slice, which is what a Modifies clause would list.
func (a passedArg) text() string {
	switch {
	case a.packed && len(a.pack) == 0:
		return "nil"
	case a.packed:
		parts := make([]string, len(a.pack))
		for i, e := range a.pack {
			parts[i] = types.ExprString(e)
		}
		return strings.Join(parts, ", ")
	}
	return types.ExprString(a.expr)
}

// evalPassed evaluates what a call gives one parameter: the argument as the
// parameter takes it, or, for a pack, a new slice of its arguments, each
// converted to the element type. The arguments are operands of the call
// like any other, and the slice is made once they have all been evaluated.
// Nothing can refer to its array yet, so it is apart from every argument,
// though what its elements refer to is the caller's.
func (v *fnVerifier) evalPassed(a passedArg, st *state, guard []*logic.Term) value {
	t := a.param.Type()
	if !a.packed {
		if _, ok := layoutOf(t); !ok {
			v.unsupported(a.expr.Pos(), fmt.Sprintf("arguments of type %s are not supported", t))
		}
		return v.evalAs(a.expr, t, st, guard)
	}
	if len(a.pack) == 0 {
		return zeroValue(t)
	}
	elem := elemType(t)
	if _, ok := layoutOf(elem); !ok {
		v.unsupported(a.pack[0].Pos(), fmt.Sprintf("arguments of type %s are not supported", elem))
	}
	elements := make([]value, len(a.pack))
	for i, e := range a.pack {
		elements[i] = v.settled(st, guard, v.evalAs(e, elem, st, guard), elem)
	}
	n := logic.IntLit(int64(len(a.pack)))
	return v.allocSlice(st, elem, elements, n, n)
}
