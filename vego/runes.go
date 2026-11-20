package vego

import (
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// runeString gives string(x) for an integer x: the UTF-8 encoding of the
// code point x, as Go writes it. A value that is no code point, being
// negative, above 0x10FFFF, or a surrogate, gives the encoding of U+FFFD.
// The integer is named once, so that the facts, which mention it in every
// case, hold it once.
func (v *fnVerifier) runeString(st *state, x *logic.Term, to types.Type) value {
	x = v.named(st, "rune", x)
	s := v.fresh("runes", logic.IntSeq)
	st.assume(utf8Facts(x, s))
	result := value{s}
	v.noteTyped(st, result, to)
	return result
}

// utf8Facts states that the string s is the UTF-8 encoding of the integer
// r, as string(r) gives it in Go: one byte below 0x80, two below 0x800,
// three below 0x10000, four up to 0x10FFFF, and the three bytes of U+FFFD
// for a negative number, one above 0x10FFFF, or a surrogate (0xD800 to
// 0xDFFF). TestRuneString checks it against Go.
func utf8Facts(r, s *logic.Term) *logic.Term {
	n := logic.IntLit
	in := func(lo, hi int64) *logic.Term { return logic.And(logic.Le(n(lo), r), logic.Le(r, n(hi))) }
	bytes := func(parts ...*logic.Term) *logic.Term {
		facts := []*logic.Term{logic.Eq(logic.Len(s), n(int64(len(parts))))}
		for i, part := range parts {
			facts = append(facts, logic.Eq(logic.Select(s, n(int64(i))), part))
		}
		return logic.And(facts...)
	}
	// In every case below r is at least 0, where Go's division is the
	// mathematical one.
	shifted := func(d int64) *logic.Term { return logic.Div(r, n(d)) }
	low := func(t *logic.Term) *logic.Term { return logic.Add(n(0x80), logic.Mod(t, n(64))) }
	surrogate := in(0xD800, 0xDFFF)
	return logic.And(
		logic.Implies(logic.Or(logic.Lt(r, n(0)), logic.Lt(n(0x10FFFF), r), surrogate), bytes(n(0xEF), n(0xBF), n(0xBD))),
		logic.Implies(in(0, 0x7F), bytes(r)),
		logic.Implies(in(0x80, 0x7FF), bytes(logic.Add(n(0xC0), shifted(64)), low(r))),
		logic.Implies(logic.And(in(0x800, 0xFFFF), logic.Not(surrogate)),
			bytes(logic.Add(n(0xE0), shifted(4096)), low(shifted(64)), low(r))),
		logic.Implies(in(0x10000, 0x10FFFF),
			bytes(logic.Add(n(0xF0), shifted(262144)), low(shifted(4096)), low(shifted(64)), low(r))),
	)
}
