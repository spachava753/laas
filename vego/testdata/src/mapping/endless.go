package mapping

// A loop that adds a key on every pass never ends: the map grows until the
// program runs out of memory. The bound on the number of keys rests on
// memory alone, so a Variant may not rest on it (F1 of the design review of
// F38).

// @Ensures n >= 0
func Counts() (n int) {
	m := map[int]bool{}
	// @Invariant Forall k in m : 0 <= k And k < |m|
	// @Variant MaxInt - |m|
	for len(m) >= 0 { // want `vego: loop variant may be negative: MaxInt - \|m\|; it holds only because a map cannot have more keys than memory can hold`
		m[len(m)] = true
	}
	return len(m)
}

// @Ensures n = 7
func Forever() (n int) {
	m := map[int]bool{}
	// @Invariant Forall k in m : 0 <= k And k < |m|
	// @Variant MaxAlloc - |m|
	for { // want `vego: loop variant may be negative: MaxAlloc - \|m\|; it holds only because a map cannot have more keys than memory can hold`
		m[len(m)] = true
		if len(m) == 0 {
			return 0
		}
	}
}

// @Requires m != nil
// @Requires Forall k in m : 0 <= k And k < |m|
// @Modifies m
// @Variant MaxInt - |m|
// @Ensures True
func AddsForever(m map[int]bool) { // want `vego: variant of the function may be negative: MaxInt - \|m\|; it holds only because a map cannot have more keys than memory can hold`
	m[len(m)] = true
	AddsForever(m)
}

// A Variant over what is left to do needs no bound on the keys.
// @Ensures n >= 0
func CountsInput(xs []int) (n int) {
	m := map[int]bool{}
	// @Invariant 0 <= i <= |xs|
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		m[xs[i]] = true
	}
	return len(m)
}
