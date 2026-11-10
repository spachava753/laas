package vego

import (
	"fmt"
	"go/constant"
	"go/token"
	"go/types"
	"math/big"
	"strconv"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// intRange returns the least and greatest value of an integer type on the
// platform being analysed. The logic computes with mathematical integers, so
// these bounds are what ties a program value to its Go type.
func (pv *pkgVerifier) intRange(t types.Type) (lo, hi *big.Int, ok bool) {
	basic, isBasic := t.Underlying().(*types.Basic)
	if !isBasic || basic.Info()&types.IsInteger == 0 || basic.Info()&types.IsUntyped != 0 || basic.Kind() == types.Uintptr {
		return nil, nil, false
	}
	bits := uint(pv.pass.TypesSizes.Sizeof(basic)) * 8
	if basic.Info()&types.IsUnsigned != 0 {
		hi = new(big.Int).Lsh(big.NewInt(1), bits)
		return big.NewInt(0), hi.Sub(hi, big.NewInt(1)), true
	}
	hi = new(big.Int).Lsh(big.NewInt(1), bits-1)
	return new(big.Int).Neg(hi), new(big.Int).Sub(hi, big.NewInt(1)), true
}

// typeFact states what a value's Go type guarantees: an integer lies in the
// range of its type, and a slice is no longer than the largest int.
func (pv *pkgVerifier) typeFact(value *logic.Term, t types.Type) *logic.Term {
	if value.Sort.IsSeq() {
		_, most, _ := pv.intRange(types.Typ[types.Int])
		return logic.Le(logic.Len(value), logic.BigLit(most))
	}
	lo, hi, ok := pv.intRange(t)
	if !ok || value.Sort != logic.Int {
		return logic.True()
	}
	return logic.And(logic.Le(logic.BigLit(lo), value), logic.Le(value, logic.BigLit(hi)))
}

// checkFits requires the mathematical result of an operation to be a value of
// its Go type. Go would wrap silently; verified code may not overflow.
func (v *fnVerifier) checkFits(st *state, guard []*logic.Term, value *logic.Term, t types.Type, pos token.Pos, what string) {
	v.check(st, guard, v.typeFact(value, t), pos, "%s may overflow %s", what, types.TypeString(t, nil))
}

// namedLimit resolves the names annotations may use for the limits of the
// integer types, following package math: MaxInt, MinInt, MaxInt8 ... MaxInt64,
// MinInt8 ... MinInt64, MaxUint, MaxUint8 ... MaxUint64.
func (pv *pkgVerifier) namedLimit(name string) (*logic.Term, bool) {
	kinds := map[string]types.BasicKind{
		"Int": types.Int, "Int8": types.Int8, "Int16": types.Int16, "Int32": types.Int32, "Int64": types.Int64,
		"Uint": types.Uint, "Uint8": types.Uint8, "Uint16": types.Uint16, "Uint32": types.Uint32, "Uint64": types.Uint64,
	}
	kind, known := kinds[name[min(3, len(name)):]]
	if !known {
		return nil, false
	}
	lo, hi, _ := pv.intRange(types.Typ[kind])
	switch {
	case strings.HasPrefix(name, "Max"):
		return logic.BigLit(hi), true
	case strings.HasPrefix(name, "Min") && lo.Sign() < 0:
		return logic.BigLit(lo), true
	}
	return nil, false
}

// constantNamed resolves a name that does not denote a variable: a constant
// of the package or one of the integer limits.
func (pv *pkgVerifier) constantNamed(obj types.Object, name string) (*logic.Term, error) {
	if c, ok := obj.(*types.Const); ok {
		if literal, ok := literalOf(c.Val()); ok {
			return literal, nil
		}
	}
	if limit, ok := pv.namedLimit(name); ok && obj == nil {
		return limit, nil
	}
	return nil, fmt.Errorf("unknown name %s", name)
}

// literalOf converts an integer or boolean constant to a term.
func literalOf(value constant.Value) (*logic.Term, bool) {
	switch value.Kind() {
	case constant.Bool:
		return logic.BoolLit(constant.BoolVal(value)), true
	case constant.Int:
		number, ok := new(big.Int).SetString(value.ExactString(), 10)
		return logic.BigLit(number), ok
	}
	return nil, false
}

// operation names an operation for an overflow diagnostic.
func operation(op token.Token) string {
	switch op {
	case token.ADD, token.INC:
		return "addition"
	case token.SUB, token.DEC:
		return "subtraction"
	case token.MUL:
		return "multiplication"
	}
	return "operation " + strconv.Quote(op.String())
}
