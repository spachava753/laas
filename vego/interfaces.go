package vego

import (
	"fmt"
	"go/ast"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// An interface value other than an error is one reference, zero exactly
// for the nil interface. Nothing else is known of it: which type it holds,
// and what value of that type, is not modelled, so two interface values can
// only be compared with nil, in code and in formulas. Go's == on two
// interface values compares the dynamic types and then the values, and
// panics when both hold the same type and that type is not comparable;
// none of that can be decided without the dynamic types.
//
// Converting a concrete value to an interface gives a reference that is
// not zero, also for a nil pointer, which in Go makes an interface that is
// not nil. Converting one interface value to another keeps the reference,
// so the nil interface stays nil.

// ifaceCompared is the message for == and != on interface values with
// anything but nil.
const ifaceCompared = "comparing interface values is not supported yet: == compares the types and values they hold, " +
	"which are not known, and panics when both hold the same type and it is not comparable; compare with nil instead"

// ifaceAsserted is the message for type assertions and type switches.
const ifaceAsserted = "type assertions and type switches are not supported yet: the type an interface value holds is not known"

// interfaceValue evaluates an expression that is assigned to something of
// an interface type other than error, where Go converts it to that type.
func (v *fnVerifier) interfaceValue(e ast.Expr, want types.Type, st *state, guard []*logic.Term) value {
	from := v.info.TypeOf(e)
	switch {
	case types.Identical(from, want):
		return v.eval(e, st, guard)
	case isIface(from):
		// The value keeps its methods, so a method of want must be one of
		// them, the very declaration, and so with the same contract.
		if method := v.foreignMethod(from, want); method != nil {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s, a %s, to %s is not supported: %s declares %s itself, "+
				"which %s does not have; an interface value can be converted only to an interface whose methods are "+
				"declarations it has, as through embedding, or to any", types.ExprString(e), from, want, want, method.Name(), from))
		}
		return v.eval(e, st, guard)
	case isError(from):
		if want.Underlying().(*types.Interface).NumMethods() > 0 {
			v.unsupported(e.Pos(), fmt.Sprintf("converting an error to %s is not supported; only any can hold an error", want))
		}
		// The nil error becomes the nil interface, and any other error an
		// interface value that is not nil.
		err := v.eval(e, st, guard)[0]
		held := v.fresh("iface", logic.Ref)
		st.assume(logic.Iff(logic.Eq(held, logic.RefLit(0)), logic.IsNil(err)))
		return value{held}
	case types.IsInterface(from):
		v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to %s is not supported", from, want))
	case want.Underlying().(*types.Interface).NumMethods() > 0:
		v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to the interface %s is not supported yet", from, want))
	}
	// An interface without methods can hold anything. Nothing can be done
	// with what it holds but pass it on.
	v.eval(e, st, guard)
	held := v.fresh("iface", logic.Ref)
	st.assume(logic.Ne(held, logic.RefLit(0)))
	return value{held}
}

// foreignMethod returns a method of the interface want that the interface
// from does not have as the same declaration, or nil if there is none.
func (v *fnVerifier) foreignMethod(from, want types.Type) *types.Func {
	have := from.Underlying().(*types.Interface)
	need := want.Underlying().(*types.Interface)
	for method := range need.Methods() {
		found := false
		for own := range have.Methods() {
			if own == method {
				found = true
				break
			}
		}
		if !found {
			return method
		}
	}
	return nil
}
