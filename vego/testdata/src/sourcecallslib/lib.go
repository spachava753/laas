// Package sourcecallslib exports a function whose parameter has a contract
// under Calls, which its contract fact carries to importers.
package sourcecallslib

// Limit bounds what Each hands f.
const Limit = 100

// Each calls f with every element of xs.
//
// @Calls f(x) When 0 <= x < Limit
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < Limit
// @Ensures True
func Each(xs []int, f func(int)) {
	for _, x := range xs {
		f(x)
	}
}
