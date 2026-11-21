package vego

import (
	"math"
	"math/big"
	"math/rand/v2"
	"slices"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// TestRuneString checks utf8Facts, which string(x) of an integer assumes,
// against Go: for each value, the facts must allow the string Go makes and
// no other, of any length or with any other byte.
func TestRuneString(t *testing.T) {
	parallel(t)
	z3, err := solver.Open("", testCache)
	if err != nil {
		t.Fatal(err)
	}
	r, s := logic.Const("r", logic.Int), logic.Const("s", logic.IntSeq)
	facts := utf8Facts(r, s)
	sat := func(known ...*logic.Term) bool {
		return z3.Check(append([]*logic.Term{facts}, known...), solver.Options{}) == solver.Refuted
	}
	check := func(value *logic.Term, want string, label string) {
		t.Helper()
		is := logic.Eq(r, value)
		matches := []*logic.Term{logic.Eq(logic.Len(s), logic.IntLit(int64(len(want))))}
		for i := range len(want) {
			matches = append(matches, logic.Eq(logic.Select(s, logic.IntLit(int64(i))), logic.IntLit(int64(want[i]))))
		}
		if !sat(is, logic.And(matches...)) {
			t.Fatalf("%s: the facts rule out string(%s) = %q", label, value, want)
		}
		if sat(is, logic.Not(logic.And(matches...))) {
			t.Fatalf("%s: the facts allow string(%s) to differ from %q", label, value, want)
		}
	}
	var values []int64
	for _, boundary := range []int64{0, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xD800, 0xDFFF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF, 0x110000} {
		values = append(values, boundary-1, boundary, boundary+1)
	}
	values = append(values, math.MinInt32, math.MaxInt32, math.MinInt64, math.MaxInt64, 'a', '/', 'é', '€', '😀')
	random := rand.New(rand.NewPCG(1, 2))
	for range 40 {
		values = append(values, random.Int64N(0x120000)-0x100)
	}
	for _, value := range values {
		at := logic.IntLit(value)
		// The runtime gives U+FFFD when int64(rune(x)) != x and does not
		// truncate, as string(int64(1<<32 + 65)) shows; vet refuses string
		// of an int64 in a test, so the test cannot ask Go for it here.
		asRune := rune(value)
		if int64(asRune) != value {
			asRune = -1
		}
		check(at, string(asRune), "int64")
		if value >= math.MinInt32 && value <= math.MaxInt32 {
			check(at, string(rune(value)), "rune")
		}
		if value >= 0 && value <= math.MaxUint8 {
			check(at, string(rune(byte(value))), "byte")
		}
		if value >= math.MinInt8 && value <= math.MaxInt8 {
			check(at, string(rune(int8(value))), "int8")
		}
	}
	// Every code point, and the values just outside, by evaluating the
	// facts in Go: they hold of the string Go makes, and fail when one byte
	// or the length differs. A byte changes inside a range at every
	// multiple of 64, 4096, and 262144, which the values above do not all
	// reach.
	for value := int64(-1); value <= 0x110000; value++ {
		want := []byte(string(rune(value)))
		if !holdsRune(facts, value, want) {
			t.Fatalf("the facts do not hold of string(%d) = %q", value, want)
		}
		for i := range want {
			for _, delta := range []byte{1, 255} {
				changed := slices.Clone(want)
				changed[i] += delta
				if holdsRune(facts, value, changed) {
					t.Fatalf("the facts hold of %q for string(%d), which is %q", changed, value, want)
				}
			}
		}
		if holdsRune(facts, value, append(slices.Clone(want), want[0])) || holdsRune(facts, value, want[:len(want)-1]) {
			t.Fatalf("the facts hold of another length for string(%d)", value)
		}
	}
	// A uint64 above MaxInt64 is no code point either, and Go gives
	// U+FFFD for it, as for every value outside the range of a rune.
	for _, huge := range []uint64{1 << 63, math.MaxUint64} {
		check(logic.BigLit(new(big.Int).SetUint64(huge)), string(rune(0xFFFD)), "uint64")
	}
}

// holdsRune evaluates utf8Facts of the constants r and s for one integer and
// one string of bytes, with Go's division, which is exact for the operands
// the facts divide.
func holdsRune(facts *logic.Term, r int64, s []byte) bool {
	var number func(t *logic.Term) int64
	var holds func(t *logic.Term) bool
	number = func(t *logic.Term) int64 {
		switch t.Op {
		case logic.OpIntLit:
			return t.Val
		case logic.OpConst:
			return r
		case logic.OpAdd:
			return number(t.Args[0]) + number(t.Args[1])
		case logic.OpDiv:
			return number(t.Args[0]) / number(t.Args[1])
		case logic.OpMod:
			return number(t.Args[0]) % number(t.Args[1])
		case logic.OpLen:
			return int64(len(s))
		case logic.OpSelect:
			if i := number(t.Args[1]); i >= 0 && i < int64(len(s)) {
				return int64(s[i])
			}
			return -1
		}
		panic("cannot evaluate " + t.String())
	}
	holds = func(t *logic.Term) bool {
		switch t.Op {
		case logic.OpTrue:
			return true
		case logic.OpEq:
			return number(t.Args[0]) == number(t.Args[1])
		case logic.OpLe:
			return number(t.Args[0]) <= number(t.Args[1])
		case logic.OpLt:
			return number(t.Args[0]) < number(t.Args[1])
		case logic.OpNot:
			return !holds(t.Args[0])
		case logic.OpImplies:
			return !holds(t.Args[0]) || holds(t.Args[1])
		case logic.OpAnd:
			return !slices.ContainsFunc(t.Args, func(arg *logic.Term) bool { return !holds(arg) })
		case logic.OpOr:
			return slices.ContainsFunc(t.Args, holds)
		}
		panic("cannot evaluate " + t.String())
	}
	return holds(facts)
}
