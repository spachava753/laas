package rejected

// Quantifier domains that are refused: Z when it names something, and
// anything that is not a map or the keys a loop has visited.

// ZNamed has a parameter named Z, which would give Z two meanings.
//
// @Requires Forall k in Z : k >= 0 // want `vego: in Requires annotation: Z names something here, so Forall k in Z could mean the integers or what Z names; rename it, or write an interval`
// @Ensures True
func ZNamed(Z map[int]int) {}

// ZSnapshot takes a snapshot named Z.
//
// @Ensures True
func ZSnapshot(n int) {
	// @Snapshot Z = n // want `vego: Snapshot Z: Z is a word of the annotation language; choose another name`
	// @Assert Forall k in [0, Z) : k >= 0
}

// ZVisited names the visited keys Z.
//
// @Ensures True
func ZVisited(m map[int]int) {
	// @Visited Z // want `vego: Visited Z: Z is a word of the annotation language; choose another name`
	// @Invariant |Z| >= 0
	for range m {
	}
}

// KeysOfSlice ranges over a slice as if it had keys.
//
// @Requires Forall k in s : k >= 0 // want `vego: in Requires annotation: s is not a map, so a quantifier cannot range over its keys; it ranges over Z, an interval, or the keys of a map`
// @Ensures True
func KeysOfSlice(s []int) {}

// KeysOfString ranges over a string.
//
// @Requires Forall k in s : k >= 0 // want `vego: in Requires annotation: s is not a map, so a quantifier cannot range over its keys`
// @Ensures True
func KeysOfString(s string) {}

type point struct{ x int }

// KeysOfPointer ranges over a pointer.
//
// @Requires Forall k in p : k >= 0 // want `vego: in Requires annotation: p is not a map, so a quantifier cannot range over its keys`
// @Ensures True
func KeysOfPointer(p *point) {}

// KeysOfSum ranges over something that is no path.
//
// @Requires Forall k in n + 1 : k >= 0 // want `vego: in Requires annotation: a quantifier ranges over Z, an interval, or the keys of a map reached from a variable, as in Forall k in m`
// @Ensures True
func KeysOfSum(n int) {}

// @Predicate allPositive(m) ::= Forall k in m : m[k] > 0 // want `a quantifier over the keys of a map cannot be used in a predicate definition`
