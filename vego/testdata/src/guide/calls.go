package guide

// The programs of the section on function parameters that are only
// called.

// eachScore calls f with every score.
//
// @Calls f(s) When 0 <= s <= 100
// @Requires Forall i in [0, |scores|) : 0 <= scores[i] <= 100
// @Ensures True
func eachScore(scores []int, f func(int)) {
	for _, s := range scores {
		f(s)
	}
}

// Histogram counts the scores in eleven buckets.
//
// @Requires Forall i in [0, |scores|) : 0 <= scores[i] <= 100
// @Ensures |buckets| = 11
func Histogram(scores []int) (buckets []int) {
	buckets = make([]int, 11)
	eachScore(scores, func(s int) {
		if buckets[s/10] < 1000000 {
			buckets[s/10]++
		}
	})
	return buckets
}

// Rescale writes the scores while eachScore walks them.
//
// @Requires |scores| > 0 And Forall i in [0, |scores|) : 0 <= scores[i] <= 100
// @Modifies scores
// @Ensures True
func Rescale(scores []int) {
	eachScore(scores, func(s int) {
		scores[0] = s // want `vego: scores\[0\] is assigned, which may be what an argument of eachScore refers to directly; a function eachScore calls under Calls may not write the elements of a slice from its first to its capacity, the struct a pointer points to, or a map that eachScore is handed beside it, in the function literal run by eachScore at calls.go:37:20`
	})
}

// Keep returns the function it is given.
//
// @Calls f()
// @Ensures True
func Keep(f func()) (g func()) {
	return f // want `vego: cannot verify Keep: the Calls annotation of Keep gives f a contract that holds only while Keep calls it, and here it is used other than by calling it: stored, returned, compared, or handed on; a function that travels needs a named function type with a contract`
}

// Passed counts the scores of 50 or more, bounded by the number of scores.
//
// @Requires Forall i in [0, |scores|) : 0 <= scores[i] <= 100
// @Ensures 0 <= passed <= |scores|
func Passed(scores []int) (passed int) {
	// @Invariant 0 <= passed <= |scores|
	eachScore(scores, func(s int) {
		if s >= 50 && passed < len(scores) {
			passed++
		}
	})
	return passed
}

// Lowered keeps a variable that a run makes negative.
//
// @Requires Forall i in [0, |scores|) : 0 <= scores[i] <= 100
// @Ensures True
func Lowered(scores []int) (r int) {
	lowest := 0
	// @Invariant lowest >= 0 // want `vego: invariant may not be kept by the function literal run by eachScore: lowest >= 0`
	eachScore(scores, func(s int) {
		lowest = s - 50
	})
	return lowest
}
