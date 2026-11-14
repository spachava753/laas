package vego

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// TestBitFacts checks what bits.go tells the solver about x & y and about
// powers of two against the real operations: for each pair of small values,
// the facts together with the true result must not be contradictory. A fact
// that is false for some pair shows as a contradiction there.
func TestBitFacts(t *testing.T) {
	consistent := func(st *state, known ...*logic.Term) bool {
		hyps := append(append([]*logic.Term{}, st.hyps...), known...)
		return solver.Prove(hyps, logic.False(), solver.Options{MaxSteps: 2000}) != solver.Proved
	}
	fresh := func() (*fnVerifier, *state) {
		v := &fnVerifier{names: map[string]int{}, bitTerms: map[string]*logic.Term{}, lowZeros: map[string]uint{}, bitOrigins: map[string]bitOrigin{}}
		return v, &state{noted: map[string]bool{}}
	}
	x, y := logic.Const("x", logic.Int), logic.Const("y", logic.Int)
	is := func(term *logic.Term, value int64) *logic.Term { return logic.Eq(term, logic.IntLit(value)) }

	t.Run("and of two unknown numbers", func(t *testing.T) {
		v, st := fresh()
		and := v.bitAnd(x, y, 8, st)
		for a := int64(-9); a <= 9; a++ {
			for b := int64(-9); b <= 9; b++ {
				if !consistent(st, is(x, a), is(y, b), is(and, a&b)) {
					t.Fatalf("the facts about x & y rule out %d & %d = %d", a, b, a&b)
				}
			}
		}
	})

	t.Run("and with a constant", func(t *testing.T) {
		for _, mask := range []int64{1, 2, 3, 4, 5, 6, 7, 8, 12, 15, 16, 255, 256, -2, -8} {
			v, st := fresh()
			and := v.bitAnd(x, logic.IntLit(mask), 8, st)
			for a := int64(-40); a <= 40; a++ {
				if !consistent(st, is(x, a), is(and, a&mask)) {
					t.Fatalf("the facts about x & %d rule out %d & %d = %d", mask, a, mask, a&mask)
				}
			}
		}
	})

	t.Run("a mask of low bits or of one bit is exact", func(t *testing.T) {
		for _, mask := range []int64{1, 2, 3, 4, 7, 8, 15, 16, 255, 256} {
			v, st := fresh()
			and := v.bitAnd(x, logic.IntLit(mask), 8, st)
			for a := int64(-40); a <= 40; a++ {
				if consistent(st, is(x, a), logic.Not(is(and, a&mask))) {
					t.Fatalf("the facts about x & %d allow %d & %d to differ from %d", mask, a, mask, a&mask)
				}
			}
		}
	})

	t.Run("and with a multiple of a power of two", func(t *testing.T) {
		for _, scale := range []int64{2, 4, 8, 12} {
			v, st := fresh()
			scaled := logic.Mul(x, logic.IntLit(scale))
			and := v.bitAnd(scaled, y, 8, st)
			for a := int64(-6); a <= 6; a++ {
				for b := int64(-9); b <= 9; b++ {
					if !consistent(st, is(x, a), is(y, b), is(and, (a*scale)&b)) {
						t.Fatalf("the facts about %d*x & y rule out %d & %d = %d", scale, a*scale, b, (a*scale)&b)
					}
				}
			}
		}
	})

	t.Run("power of two", func(t *testing.T) {
		v, st := fresh()
		power := v.pow2(x, 8, st)
		for k := int64(0); k <= 8; k++ {
			if !consistent(st, is(x, k), is(power, 1<<k)) {
				t.Fatalf("the facts about 2^k rule out 2^%d = %d", k, int64(1)<<k)
			}
			// The facts must also pin the power down for a count the
			// type allows.
			wrong := logic.Not(is(power, 1<<k))
			if consistent(st, is(x, k), wrong) {
				t.Fatalf("the facts about 2^k allow 2^%d to differ from %d", k, int64(1)<<k)
			}
		}
		for _, k := range []int64{9, 20, 1000} {
			huge := logic.BigLit(new(big.Int).Lsh(big.NewInt(1), 100))
			if !consistent(st, is(x, k), logic.Eq(power, huge)) {
				t.Fatalf("the facts about 2^k rule out a large power for the count %d", k)
			}
		}
	})

	t.Run("the same operands give the same unknown", func(t *testing.T) {
		v, st := fresh()
		if first, second := v.bitAnd(x, y, 8, st), v.bitAnd(y, x, 8, st); first != second {
			t.Fatalf("x & y is %s and y & x is %s", fmt.Sprint(first), fmt.Sprint(second))
		}
	})
}
