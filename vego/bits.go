package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"math/big"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The logic computes with mathematical integers and has no notion of bits,
// so shifts and bitwise operators are expressed by arithmetic.
//
// A shift by k is a multiplication or a division by 2^k. A power of two with
// a count that is not a constant is an unknown number, of which the state is
// told how it lies between the powers for each count the type allows.
//
// x & y is an unknown number too, of which the state is told what holds of
// every two integers written in two's complement, and more when one of them
// is a constant mask. The other operators follow from it exactly:
//
//	x | y  = x + y - (x & y)
//	x ^ y  = x + y - 2*(x & y)
//	x &^ y = x - (x & y)
//	^x     = -x - 1, or for an unsigned type the greatest value minus x

// literal returns the value of a term that is an integer literal.
func literal(t *logic.Term) (*big.Int, bool) {
	switch {
	case t.Op != logic.OpIntLit:
		return nil, false
	case t.Big != nil:
		return t.Big, true
	}
	return big.NewInt(t.Val), true
}

// zeroBits returns how many low bits of a term are known to be zero from
// the way it is written: the term is a multiple of two to that power.
func (v *fnVerifier) zeroBits(t *logic.Term) uint {
	const all = 1 << 16
	if value, ok := literal(t); ok {
		if value.Sign() == 0 {
			return all
		}
		return value.TrailingZeroBits()
	}
	switch t.Op {
	case logic.OpMul:
		return min(all, v.zeroBits(t.Args[0])+v.zeroBits(t.Args[1]))
	case logic.OpAdd:
		return min(v.zeroBits(t.Args[0]), v.zeroBits(t.Args[1]))
	case logic.OpNeg:
		return v.zeroBits(t.Args[0])
	case logic.OpConst:
		return v.lowZeros[t.Name]
	}
	return 0
}

// noteOnce adds a fact about an unknown that bits.go introduced to a state
// that has not been told it yet. The unknowns are shared by all states, the
// facts are not.
func (v *fnVerifier) noteOnce(st *state, name string, facts ...*logic.Term) {
	if note := "bits " + name; !st.noted[note] {
		st.noted[note] = true
		st.assume(logic.And(facts...))
	}
}

// pow2 returns two to the power of a shift count that is known not to be
// negative. For a count that is not a constant the result is an unknown
// that stands for 2^max(k, 0), bounded from both sides for each count up to
// the number of bits; a larger count shifts everything out anyway.
func (v *fnVerifier) pow2(k *logic.Term, bits uint, st *state) *logic.Term {
	if count, ok := literal(k); ok && count.Sign() >= 0 && count.IsInt64() && count.Int64() <= 4096 {
		return logic.BigLit(new(big.Int).Lsh(big.NewInt(1), uint(count.Int64())))
	}
	key := "pow2 " + k.String()
	if v.bitTerms[key] == nil {
		v.bitTerms[key] = v.fresh("pow2", logic.Int)
	}
	power := v.bitTerms[key]
	facts := []*logic.Term{logic.Le(logic.IntLit(1), power)}
	for j := range bits + 1 {
		at, exact := logic.IntLit(int64(j)), logic.BigLit(new(big.Int).Lsh(big.NewInt(1), j))
		facts = append(facts,
			logic.Implies(logic.Le(k, at), logic.Le(power, exact)),
			logic.Implies(logic.Le(at, k), logic.Le(exact, power)))
	}
	// A wider type needs bounds for more counts than a narrower one that
	// shifted by the same count before.
	v.noteOnce(st, fmt.Sprintf("%s up to %d", key, bits), facts...)
	return power
}

// shift evaluates x << k and x >> k. A negative count panics. A shift to the
// left must not lose bits, like any other arithmetic that leaves its type.
// A shift to the right rounds towards minus infinity.
func (v *fnVerifier) shift(op token.Token, x, k *logic.Term, t types.Type, pos token.Pos, st *state, guard []*logic.Term) *logic.Term {
	least, greatest, ok := v.intRange(t)
	if !ok {
		v.unsupported(pos, fmt.Sprintf("operator %s is not supported for %s", op, t))
	}
	zero := logic.IntLit(0)
	v.check(st, guard, logic.Le(zero, k), pos, "shift count may be negative")
	power := v.pow2(k, uint(greatest.BitLen())+1, st)
	if op == token.SHL {
		result := logic.Mul(x, power)
		v.checkFits(st, guard, result, t, pos, "shift")
		return result
	}
	down := logic.Div(x, power)
	if least.Sign() == 0 {
		return down
	}
	// Go's division rounds towards zero, so a negative number is shifted by
	// way of the number that is not negative and has the opposite bits.
	one := logic.IntLit(1)
	return logic.Ite(logic.Le(zero, x), down, logic.Sub(logic.Neg(logic.Div(logic.Sub(logic.Neg(x), one), power)), one))
}

// bitOrigin says how a term was made from two operands by a bitwise
// operator, for the identities that bitAnd applies.
type bitOrigin struct {
	op   token.Token
	x, y string
}

// bitAnd returns x & y: an unknown number, the same one for the same two
// operands in either order, of which the state is told what follows from
// the operands. bits is the width of the type.
func (v *fnVerifier) bitAnd(x, y *logic.Term, bits uint, st *state) *logic.Term {
	if y.String() < x.String() {
		x, y = y, x
	}
	zero := logic.IntLit(0)
	if x.String() == y.String() {
		return x
	}
	// An operand that was itself made with the other one: the bits of m
	// are all set in x | m, all clear in x &^ m, and x & m has none but
	// bits of m.
	for _, pair := range [][2]*logic.Term{{x, y}, {y, x}} {
		made, mask := v.bitOrigins[pair[0].String()], pair[1].String()
		switch {
		case made.op == token.OR && (made.x == mask || made.y == mask):
			return pair[1]
		case made.op == token.AND_NOT && made.y == mask:
			return zero
		case made.op == token.AND && (made.x == mask || made.y == mask):
			return pair[0]
		}
	}
	for _, pair := range [][2]*logic.Term{{x, y}, {y, x}} {
		if mask, ok := literal(pair[0]); ok && mask.Sign() == 0 {
			return zero
		} else if ok && mask.Cmp(big.NewInt(-1)) == 0 {
			return pair[1]
		}
	}
	if a, ok := literal(x); ok {
		if b, ok := literal(y); ok {
			return logic.BigLit(new(big.Int).And(a, b))
		}
	}
	key := "and " + x.String() + " & " + y.String()
	if v.bitTerms[key] == nil {
		v.bitTerms[key] = v.fresh("and", logic.Int)
		// A bit that is zero in either operand is zero in the result.
		v.lowZeros[v.bitTerms[key].Name] = max(v.zeroBits(x), v.zeroBits(y))
	}
	and := v.bitTerms[key]
	negative := func(t *logic.Term) *logic.Term { return logic.Lt(t, zero) }
	// What holds of any two integers in two's complement: the result has
	// the sign bit only if both have it, has no bit that one of them lacks,
	// and, since x | y = x + y - (x & y) has the sign bit if either has
	// it, cannot be small when both are negative.
	facts := []*logic.Term{
		logic.Implies(logic.Le(zero, x), logic.And(logic.Le(zero, and), logic.Le(and, x))),
		logic.Implies(logic.Le(zero, y), logic.And(logic.Le(zero, and), logic.Le(and, y))),
		logic.Implies(logic.And(negative(x), negative(y)),
			logic.And(negative(and), logic.Le(and, x), logic.Le(and, y), logic.Le(logic.Add(logic.Add(x, y), logic.IntLit(1)), and))),
	}
	// Two numbers that fit in so many bits have an x | y that fits in as
	// many, and x | y is x + y - (x & y).
	for n := uint(1); n < bits; n++ {
		limit := logic.BigLit(new(big.Int).Lsh(big.NewInt(1), n))
		small := logic.And(logic.Le(zero, x), logic.Lt(x, limit), logic.Le(zero, y), logic.Lt(y, limit))
		facts = append(facts, logic.Implies(small, logic.Lt(logic.Sub(logic.Add(x, y), and), limit)))
	}
	for _, pair := range [][2]*logic.Term{{x, y}, {y, x}} {
		// An operand whose low bits are zero wipes out one that has only
		// such bits.
		if low := v.zeroBits(pair[0]); low > 0 && low < 4096 {
			limit := logic.BigLit(new(big.Int).Lsh(big.NewInt(1), low))
			facts = append(facts, logic.Implies(logic.And(logic.Le(zero, pair[1]), logic.Lt(pair[1], limit)), logic.Eq(and, zero)))
		}
		mask, ok := literal(pair[0])
		if !ok || mask.Sign() <= 0 {
			continue
		}
		other, next := pair[1], new(big.Int).Add(mask, big.NewInt(1))
		switch {
		case new(big.Int).And(mask, next).Sign() == 0:
			// A mask of the low bits takes the remainder, counted
			// upwards from a multiple of the modulus.
			modulus := logic.BigLit(next)
			facts = append(facts,
				logic.Implies(logic.Le(zero, other), logic.Eq(and, logic.Mod(other, modulus))),
				logic.Implies(negative(other), logic.Eq(and, logic.Mod(logic.Add(logic.Mod(other, modulus), modulus), modulus))))
		case new(big.Int).And(mask, new(big.Int).Sub(mask, big.NewInt(1))).Sign() == 0:
			// A mask of one bit yields that bit or nothing.
			bit := logic.BigLit(mask)
			facts = append(facts,
				logic.Or(logic.Eq(and, zero), logic.Eq(and, bit)),
				logic.Implies(logic.Le(zero, other), logic.Eq(and, logic.Mul(logic.Mod(logic.Div(other, bit), logic.IntLit(2)), bit))))
		}
	}
	v.noteOnce(st, key, facts...)
	return and
}

// bitwise evaluates x & y, x | y, x ^ y, and x &^ y. The result of any of
// them on two values of a type is a value of the type.
func (v *fnVerifier) bitwise(op token.Token, x, y *logic.Term, t types.Type, pos token.Pos, st *state) *logic.Term {
	_, greatest, ok := v.intRange(t)
	if !ok {
		v.unsupported(pos, fmt.Sprintf("operator %s is not supported for %s", op, t))
	}
	and := v.bitAnd(x, y, uint(greatest.BitLen())+1, st)
	result := and
	switch op {
	case token.OR:
		result = logic.Sub(logic.Add(x, y), and)
	case token.XOR:
		result = logic.Sub(logic.Add(x, y), logic.Mul(logic.IntLit(2), and))
	case token.AND_NOT:
		result = logic.Sub(x, and)
	}
	st.assume(logic.Implies(logic.And(v.typeFact(x, t), v.typeFact(y, t)), v.typeFact(result, t)))
	v.bitOrigins[result.String()] = bitOrigin{op, x.String(), y.String()}
	return result
}

// complement evaluates ^x.
func (v *fnVerifier) complement(x *logic.Term, t types.Type, pos token.Pos) *logic.Term {
	least, greatest, ok := v.intRange(t)
	if !ok {
		v.unsupported(pos, fmt.Sprintf("operator ^ is not supported for %s", t))
	}
	if least.Sign() == 0 {
		return logic.Sub(logic.BigLit(greatest), x)
	}
	return logic.Sub(logic.Neg(x), logic.IntLit(1))
}
