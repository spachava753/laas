package guide

// Samples holds values.
type Samples struct {
	Values []int
	n      int
}

// Collect appends n values to j.Values.
//
// @Requires j != nil And 0 <= n < 1000 And |j.Values| < 1000
// @Modifies j, j.Values
// @Ensures |j.Values'| = |j.Values| + n
func Collect(j *Samples, n int) {
	// @Invariant |j.Values| = |old(j.Values)| + i
	for i := range n {
		j.Values = append(j.Values, i)
	}
}

// tick counts a value.
//
// @Requires j != nil And j.n < 1000000
// @Modifies j.n
// @Ensures j.n' = j.n + 1
func tick(j *Samples) {
	j.n++
}

// CollectCounted appends n values and counts them.
//
// @Requires j != nil And 0 <= n < 1000 And |j.Values| < 1000 And j.n < 1000
// @Modifies j, j.Values
// @Ensures |j.Values'| = |j.Values| + n
func CollectCounted(j *Samples, n int) {
	// @Invariant |j.Values| = |old(j.Values)| + i And j.n = old(j.n) + i
	for i := range n {
		j.Values = append(j.Values, i) // want `vego: append may write into the capacity of j\.Values, which CollectCounted may not modify: nothing its // @Modifies clauses list is known to cover it`
		tick(j)
	}
}

// CollectSaid says where j.Values is.
//
// @Requires j != nil And 0 <= n < 1000 And |j.Values| < 1000 And j.n < 1000
// @Modifies j, j.Values
// @Ensures |j.Values'| = |j.Values| + n
func CollectSaid(j *Samples, n int) {
	// @Invariant |j.Values| = |old(j.Values)| + i And j.n = old(j.n) + i
	// @Invariant fresh(j.Values) Or within(j.Values, old(j.Values))
	for i := range n {
		j.Values = append(j.Values, i)
		tick(j)
	}
}
