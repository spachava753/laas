package funcvalues

import "keeper"

// The case that the wording of runs exists for. A trusted function that
// keeps code it was given lets another trusted function run that code later,
// one whose entry received nothing and shows nothing in the trust report.
// So runs claims, for every parameter it lists, that the function runs the
// code only before it returns, on the goroutine that called it, and keeps no
// value that can hold code. The entry of keeper.Keep makes that claim and
// is false: Keep keeps e, and Flush runs e.Error(), which could set s.n to
// 0 behind the proof. vego cannot see this. It is what the claim rules out.

type State struct{ n int }

// KeepThenFlush relies on the entries of Keep and Flush, and verifies.
//
// @Requires s != nil
// @Modifies s.n
// @Ensures q = 10
func KeepThenFlush(e error, s *State) (q int) {
	keeper.Keep(e)
	s.n = 1
	keeper.Flush()
	return 10 / s.n
}

// KeepUnlisted hands the error to a function whose entry does not claim to
// run it, which is refused.
//
// @Requires s != nil
// @Modifies s.n
// @Ensures True
func KeepUnlistedThenFlush(e error, s *State) {
	keeper.KeepUnlisted(e) // want `cannot verify KeepUnlistedThenFlush: e is passed to KeepUnlisted, which is trusted, and is an error whose origin is not known`
}
