package callbacks

import "sort"

// The programs of a handed function whose run meets an obligation that
// fails for certain: the run reports it, and what the trusted function
// gives the caller does not rest on it.

type stage struct{ n int }

// at needs its stage at 5.
//
// @Requires s != nil And s.n = 5
// @Ensures r
func (s *stage) at(i int) (r bool) { return true }

// AtFour hands at over with its stage at 4.
//
// @Requires s != nil And s.n = 4
// @Ensures True
func AtFour(s *stage) {
	_ = sort.Search(1, s.at) // want `vego: precondition of at may not hold: s.n = 5, in s.at run by sort.Search`
}

// AtFive hands it over with its stage at 5.
//
// @Requires s != nil And s.n = 5
// @Ensures True
func AtFive(s *stage) {
	_ = sort.Search(1, s.at)
}

// isSeven needs its argument at 7.
//
// @Requires i = 7
// @Ensures r
func isSeven(i int) (r bool) { return true }

// HandsSeven hands it to a search that asks it of 0, 1, and 2.
//
// @Ensures True
func HandsSeven() {
	_ = sort.Search(3, isSeven) // want `vego: precondition of isSeven may not hold: i = 7, in isSeven run by sort.Search`
}

// AtFourInLiteral calls at from a handed literal.
//
// @Requires s != nil And s.n = 4
// @Ensures True
func AtFourInLiteral(s *stage) {
	_ = sort.Search(1, func(i int) (r bool) { return s.at(i) }) // want `vego: precondition of at may not hold: s.n = 5, in the function literal run by sort.Search`
}

// AtFourInPlace calls at from a literal called where it is written, which
// has no consistency check after it.
//
// @Requires s != nil And s.n = 4
// @Ensures True
func AtFourInPlace(s *stage) {
	func() {
		_ = s.at(0) // want `vego: precondition of at may not hold: s.n = 5, in the function literal called at`
	}()
}

// AtFourDeferred defers the call.
//
// @Requires s != nil And s.n = 4
// @Ensures True
func AtFourDeferred(s *stage) {
	defer s.at(0) // want `vego: precondition of at may not hold: s.n = 5`
}

// probeAt is a function type with a contract.
//
// @Requires i = 5
// @Ensures r
type probeAt func(i int) (r bool)

// AtFourThroughValue calls a function value whose contract fails for
// certain.
//
// @Requires f != nil
// @Ensures True
func AtFourThroughValue(f probeAt) {
	_ = f(4) // want `vego: precondition of f may not hold: i = 5`
}

// RangeAfterFailure ranges over a map after an obligation that fails for
// certain, which the check at the range does not take for a state that no
// map can be in.
//
// @Requires s != nil And s.n = 4
// @Ensures True
func RangeAfterFailure(s *stage, m map[int]int) {
	_ = s.at(0) // want `vego: precondition of at may not hold: s.n = 5`
	for range m {
	}
}
