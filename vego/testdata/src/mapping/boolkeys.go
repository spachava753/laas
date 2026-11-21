package mapping

// The programs of maps with boolean keys, and of the bound that the number
// of values of a key type puts on the number of keys.

// BothFlags builds a map with both booleans as keys.
//
// @Ensures |result| = 2 And result[True] = 1 And result[False] = 2
func BothFlags() (result map[bool]int) {
	return map[bool]int{true: 1, false: 2}
}

// CountFlags counts the keys of a map with boolean keys, which has at most
// two.
//
// @Ensures r <= 2
func CountFlags(m map[bool]int) (r int) {
	// @Visited done
	// @Invariant r = |done|
	for range m {
		r++
	}
	return r
}

// CountFlagsOne claims at most one.
//
// @Ensures r <= 1
func CountFlagsOne(m map[bool]int) (r int) {
	// @Visited done
	// @Invariant r = |done|
	for range m {
		r++
	}
	return r // want `vego: postcondition may not hold: r <= 1`
}

// SetFlag sets one entry and keeps the other.
//
// @Requires m != nil
// @Modifies m[b]
// @Ensures has(m', b) And (Forall k in m : has(m', k))
func SetFlag(m map[bool]int, b bool) {
	m[b] = 7
}

// FlipsWhileRanging may add the other flag while it ranges.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func FlipsWhileRanging(m map[bool]int) {
	for k := range m {
		m[!k] = 1 // want `vego: this may add a key to m, the map that the loop at .* ranges over`
	}
}

// OneFlag has the key true and not false, so it has one key. That is not
// proved: outside a range over the map, its count is not tied to its keys.
//
// @Requires has(m, True) And ~has(m, False)
// @Ensures |m| = 1
func OneFlag(m map[bool]int) {} // want `vego: postcondition may not hold: \|m\| = 1`

// ThreeFlags asks for a map with three boolean keys.
//
// @Requires |m| = 3
// @Ensures True
func ThreeFlags(m map[bool]int) {} // want `vego: nothing can satisfy the Requires clauses of ThreeFlags`

// SmallKeys bounds the keys of a map with byte keys.
//
// @Ensures |m| <= 256
func SmallKeys(m map[uint8]int) {}

// SmallerKeys claims one fewer.
//
// @Ensures |m| <= 255
func SmallerKeys(m map[uint8]int) {} // want `vego: postcondition may not hold: \|m\| <= 255`
