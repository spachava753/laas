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
	for len(m) >= 0 { // want `vego: loop variant may be negative: MaxInt - \|m\|; it holds only because a map cannot have more keys than memory can hold, which does not show that a loop or a recursion ends`
		m[len(m)] = true
	}
	return len(m)
}

// @Ensures n = 7
func Forever() (n int) {
	m := map[int]bool{}
	// @Invariant Forall k in m : 0 <= k And k < |m|
	// @Variant MaxAlloc - |m|
	for { // want `vego: loop variant may be negative: MaxAlloc - \|m\|; it holds only because a map cannot have more keys than memory can hold, which does not show that a loop or a recursion ends`
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
func AddsForever(m map[int]bool) { // want `vego: variant of the function may be negative: MaxInt - \|m\|; it holds only because a map cannot have more keys than memory can hold, which does not show that a loop or a recursion ends`
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

// An invariant that only the bound on the keys preserves would carry it to
// the head, where the Variant is asked.
// @Ensures n >= 0
func ByInvariant() (n int) {
	m := map[int]bool{}
	// @Invariant Forall k in m : 0 <= k And k < |m|
	// @Invariant |m| <= MaxInt
	// @Variant MaxInt - |m|
	for len(m) >= 0 { // want `vego: loop invariant may not be preserved: \|m\| <= MaxInt; it holds only because a map cannot have more keys than memory can hold`
		m[len(m)] = true
	}
	return len(m)
}

// So would the precondition of a call that recurses, at the entry.
// @Requires m != nil
// @Requires |m| <= MaxInt
// @Requires Forall k in m : 0 <= k And k < |m|
// @Modifies m
// @Variant MaxInt - |m|
// @Ensures True
func ByRequires(m map[int]bool) {
	m[len(m)] = true
	ByRequires(m) // want `vego: precondition of ByRequires may not hold: \|m\| <= MaxInt; it holds only because a map cannot have more keys than memory can hold`
}

// A known limit, recorded and not closed (ruled by the orchestrator): a
// Variant that rests on the int range of a variable that copies the number
// of keys verifies, and every run of the loop runs out of memory, which no
// proof covers ("The machine has enough memory and stack"). A taint from a
// length to the variables that hold it would close it.
// @Ensures r >= 0
func ByInt() (r int) {
	m := map[int]bool{}
	n := 0
	// @Invariant Forall k in m : 0 <= k And k < |m|
	// @Invariant n = |m|
	// @Variant MaxInt - n
	for n >= 0 {
		m[n] = true
		n = len(m)
	}
	return n
}
