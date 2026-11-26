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
		// The bound is marked: the declared memory bounds it more tightly
		// in the second try of a size goal (sizes.go).
		return logic.Le(logic.Len(value), pv.marks().strLen)
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

// refuseTooLarge reports a value of a type that holds an array and is
// larger than one allocation can be. Go compiles such a type, and the
// program dies when it is made, with a fatal error and not a panic.
//
// Under a declared memory a value of such a type, or what a pointer to one
// points to, is reserved by its type and may never be written, so one larger
// than R, the bound on the array of every slice, would let a slice of its
// array break that bound (class N of the bound on every value, sizes.go).
func (v *fnVerifier) refuseTooLarge(pos token.Pos, t types.Type) {
	decl := v.sizesOf()
	if object, isPointer := pointee(t); isPointer && decl != nil {
		t = object
	}
	if !holdsArrayValue(t) {
		return
	}
	size := big.NewInt(v.pass.TypesSizes.Sizeof(t))
	if size.Cmp(v.maxAlloc()) > 0 {
		v.unsupported(pos, fmt.Sprintf("%s is %s bytes, more than one allocation can be (MaxAlloc, %s bytes), so no program can make it",
			types.TypeString(t, types.RelativeTo(v.pass.Pkg)), size, v.maxAlloc()))
	}
	if decl != nil && size.Cmp(decl.arrayBound()) > 0 {
		v.unsupported(pos, fmt.Sprintf("%s is %s bytes, more than the declared memory allows a value to reserve (%s bytes, five times the %s declared, "+
			"and a page), since it may be reserved and never written", types.TypeString(t, types.RelativeTo(v.pass.Pkg)), size, decl.arrayBound(), decl.written))
	}
}

// checkAlloc requires an array of count elements of the given type to be
// one the runtime will allocate.
func (v *fnVerifier) checkAlloc(st *state, guard []*logic.Term, count *logic.Term, elem types.Type, pos token.Pos, what string) {
	// The number of elements must be an int whatever their size, which is
	// all that limits elements of size zero.
	size := v.pass.TypesSizes.Sizeof(elem)
	bytes := logic.Mul(count, logic.IntLit(size))
	fits := logic.And(logic.Le(bytes, logic.BigLit(v.maxAlloc())), v.typeFact(count, types.Typ[types.Int]))
	v.checkSized(st, guard, fits, pos, "%s may be more than can be allocated", what)
}

// checkMade is checkAlloc for a make, which reserves by a number: the hint
// to declare a memory is given only where the declaration would also keep
// what it reserves within the bound on arrays (F29 of the review of 4).
func (v *fnVerifier) checkMade(st *state, guard []*logic.Term, count *logic.Term, elem types.Type, pos token.Pos, what string) {
	saved := v.alsoDeclared
	v.alsoDeclared = func(decl *sizesDecl) *logic.Term {
		return logic.Le(logic.Mul(count, logic.IntLit(v.pass.TypesSizes.Sizeof(elem))), logic.BigLit(decl.arrayBound()))
	}
	defer func() { v.alsoDeclared = saved }()
	v.checkAlloc(st, guard, count, elem, pos, what)
}

// checkReserved requires what a make reserves by a number, count elements
// of the given type that it does not write, to keep the bound on the array
// of every slice under a declared memory: count * size <= R and count an
// int (class N of the bound on every value, sizes.go). R is below MaxAlloc,
// so it implies what checkAlloc asks, which is not asked then (F22 of the
// review of step 2c). It reports whether the declaration was in effect.
func (v *fnVerifier) checkReserved(st *state, guard []*logic.Term, count *logic.Term, elem types.Type, pos token.Pos, what string) bool {
	decl := v.sizesOf()
	if decl == nil {
		return false
	}
	bytes := logic.Mul(count, logic.IntLit(v.pass.TypesSizes.Sizeof(elem)))
	v.checkDeclared(st, guard, logic.And(logic.Le(bytes, logic.BigLit(decl.arrayBound())), v.typeFact(count, types.Typ[types.Int])), pos,
		"%s may reserve more than the declared memory allows a value to: at most %s bytes, five times the %s declared, and a page; "+
			"a size that a number gives is not bounded by what the machines hold, so bound it", what, decl.arrayBound(), decl.written)
	return true
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
