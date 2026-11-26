package guide

// The programs of "How many keys a map can have" and of "The machine has
// enough memory and stack" in "What a proof assumes".

// @Ensures n >= 0
func AddsKeys() (n int) {
	m := map[int]bool{}
	// @Invariant Forall k in m : 0 <= k And k < |m|
	// @Variant MaxInt - |m|
	for len(m) >= 0 { // want `vego: loop variant may be negative: MaxInt - \|m\|; it holds only because a map cannot have more keys than memory can hold, which does not show that a loop or a recursion ends: one that adds keys until memory runs out does not end`
		m[len(m)] = true
	}
	return len(m)
}

// ByInt verifies and never ends: the bound reaches the Variant through the
// int range of n, which vego does not follow (a known limit).
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
