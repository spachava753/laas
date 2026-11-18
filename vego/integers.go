package vego

import (
	"fmt"
	"go/build"
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
// range of its type, and a string is no longer than an allocation can be
// and than an int can count, whichever is less on the platform.
func (pv *pkgVerifier) typeFact(value *logic.Term, t types.Type) *logic.Term {
	if value.Sort.IsSeq() {
		longest := pv.maxAlloc()
		if _, most, _ := pv.intRange(types.Typ[types.Int]); most.Cmp(longest) < 0 {
			longest = most
		}
		return logic.Le(logic.Len(value), logic.BigLit(longest))
	}
	lo, hi, ok := pv.intRange(t)
	if !ok || value.Sort != logic.Int {
		return logic.True()
	}
	return logic.And(logic.Le(logic.BigLit(lo), value), logic.Le(value, logic.BigLit(hi)))
}

// maxAlloc returns the most bytes one allocation may have on the platform
// being analysed, which is the runtime's own limit: it panics when asked for
// more. Every array and string that exists is therefore no larger.
func (pv *pkgVerifier) maxAlloc() *big.Int {
	goos, goarch := build.Default.GOOS, build.Default.GOARCH
	wide := pv.pass.TypesSizes.Sizeof(types.Typ[types.Uintptr]) >= 8
	bits := uint(32)
	switch {
	case goarch == "mips" || goarch == "mipsle":
		bits = 31
	case goos == "ios" && goarch == "arm64":
		bits = 40
	case wide && goarch != "wasm":
		bits = 48
	}
	limit := new(big.Int).Lsh(big.NewInt(1), bits)
	if !wide {
		limit.Sub(limit, big.NewInt(1))
	}
	return limit
}

// checkAlloc requires an array of count elements of the given type to be
// one the runtime will allocate.
func (v *fnVerifier) checkAlloc(st *state, guard []*logic.Term, count *logic.Term, elem types.Type, pos token.Pos, what string) {
	// The number of elements must be an int whatever their size, which is
	// all that limits elements of size zero.
	size := v.pass.TypesSizes.Sizeof(elem)
	bytes := logic.Mul(count, logic.IntLit(size))
	fits := logic.And(logic.Le(bytes, logic.BigLit(v.maxAlloc())), v.typeFact(count, types.Typ[types.Int]))
	v.check(st, guard, fits, pos, "%s may be more than can be allocated", what)
}

// checkFits requires the mathematical result of an operation to be a value of
// its Go type. Go would wrap silently; verified code may not overflow.
func (v *fnVerifier) checkFits(st *state, guard []*logic.Term, value *logic.Term, t types.Type, pos token.Pos, what string) {
	v.check(st, guard, v.typeFact(value, t), pos, "%s may overflow %s", what, types.TypeString(t, nil))
}

// namedLimit resolves the names annotations may use for the limits of the
// integer types, following package math: MaxInt, MinInt, MaxInt8 ... MaxInt64,
// MinInt8 ... MinInt64, MaxUint, MaxUint8 ... MaxUint64. MaxAlloc is the
// largest number of bytes one allocation can have, which is what limits the
// length of a string or of a slice of bytes.
func (pv *pkgVerifier) namedLimit(name string) (*logic.Term, bool) {
	if name == "MaxAlloc" {
		return logic.BigLit(pv.maxAlloc()), true
	}
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
