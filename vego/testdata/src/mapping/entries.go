package mapping

// The programs of Modifies entries of maps: m[k] names the entry of key k
// of a map whose values are not references, and a caller keeps every
// other key and knows how many keys the map has.

// BumpEntry adds one to the value of one key.
//
// @Requires m != nil And m[k] < 1000
// @Modifies m[k]
// @Ensures has(m', k) And m'[k] = m[k] + 1
func BumpEntry(m map[string]int, k string) {
	m[k] = m[k] + 1
}

// KeepsOther keeps the value of another key across the call.
//
// @Requires m != nil And m[k] < 1000 And m[j] = 5 And k != j
// @Modifies m
// @Ensures m'[j] = 5 And |m'| >= |m|
func KeepsOther(m map[string]int, k, j string) {
	BumpEntry(m, k)
}

// KeepsOtherMaybeSame keeps it too, though j may be k.
//
// @Requires m != nil And m[k] < 1000 And m[j] = 5
// @Modifies m
// @Ensures m'[j] = 5
func KeepsOtherMaybeSame(m map[string]int, k, j string) {
	BumpEntry(m, k)
} // want `vego: postcondition may not hold: m'\[j\] = 5`

// CountKept knows that a key that was there leaves the count as it was.
//
// @Requires m != nil And has(m, k) And m[k] < 1000
// @Modifies m
// @Ensures |m'| = |m|
func CountKept(m map[string]int, k string) {
	BumpEntry(m, k)
}

// WritesAnother writes a key its Modifies clause does not list.
//
// @Requires m != nil
// @Modifies m[k]
// @Ensures True
func WritesAnother(m map[string]int, k, j string) {
	m[j] = 1 // want `vego: m\[j\] is assigned, which WritesAnother may not modify: nothing its // @Modifies clauses list is known to cover it`
}

// WritesWhole writes the whole map through a callee that lists it, which
// one entry does not cover.
//
// @Requires m != nil
// @Modifies m[k]
// @Ensures True
func WritesWhole(m map[string]int, k string) {
	DropNegative(m) // want `vego: DropNegative may modify m, which WritesWhole may not modify`
}

type marks map[string]bool
type marked map[string]marks

// SetEdge writes one entry of the map held under from.
//
// @Requires g[from] != nil
// @Modifies g[from][to]
// @Ensures g'[from][to]
func SetEdge(g marked, from, to string) {
	g[from][to] = true
}

// SetEdgeKeeps keeps the other entries of that map across the call.
//
// @Requires g[from] != nil And g[from]["x"] And to != "x"
// @Modifies g[from]
// @Ensures g'[from]["x"]
func SetEdgeKeeps(g marked, from, to string) {
	SetEdge(g, from, to)
}

// AppendEntry writes an entry of a map of slices, which m[k] does not
// cover: it names the slice that the value is.
//
// @Requires g != nil And |g[k]| < 1000
// @Modifies g[k]
// @Ensures True
func AppendEntry(g map[string][]int, k string) {
	g[k] = append(g[k], 1) // want `vego: g\[k\] is assigned, which AppendEntry may not modify; list the whole map in a // @Modifies clause: an entry of a map whose values are pointers, slices, maps, or interface values is covered only by the map`
}

// setTwo sets one entry of each of two maps, which may be one map, and
// the keys may be one key.
//
// @Requires a != nil And b != nil
// @Modifies a[k], b[j]
// @Ensures has(a', k) And has(b', j)
func setTwo(a, b map[int]int, k, j int) {
	a[k] = 1
	b[j] = 1
}

// SameMapSameKey adds one key through both entries.
//
// @Requires a != nil And ~has(a, 1)
// @Modifies a
// @Ensures |a'| = |a| + 1
func SameMapSameKey(a map[int]int) {
	setTwo(a, a, 1, 1)
}

// SameMapSameKeyTwice claims two.
//
// @Requires a != nil And ~has(a, 1)
// @Modifies a
// @Ensures |a'| = |a| + 2
func SameMapSameKeyTwice(a map[int]int) {
	setTwo(a, a, 1, 1)
} // want `vego: postcondition may not hold: \|a'\| = \|a\| \+ 2`

// SameMapTwoKeys adds two keys.
//
// @Requires a != nil And ~has(a, 1) And ~has(a, 2)
// @Modifies a
// @Ensures |a'| = |a| + 2
func SameMapTwoKeys(a map[int]int) {
	setTwo(a, a, 1, 2)
}

// TwoMapsOneKeyEach adds one key to each of two maps.
//
// @Requires a != nil And b != nil And a != b And ~has(a, 1) And ~has(b, 1)
// @Modifies a, b
// @Ensures |a'| = |a| + 1 And |b'| = |b| + 1
func TwoMapsOneKeyEach(a, b map[int]int) {
	setTwo(a, b, 1, 1)
}

// TwoMapsTwo claims two keys in a, which it has only when b is a.
//
// @Requires a != nil And b != nil And ~has(a, 1) And ~has(b, 2)
// @Modifies a, b
// @Ensures |a'| = |a| + 2
func TwoMapsTwo(a, b map[int]int) {
	setTwo(a, b, 1, 2)
} // want `vego: postcondition may not hold: \|a'\| = \|a\| \+ 2`

// dropEntry deletes one key.
//
// @Modifies m[k]
// @Ensures ~has(m', k)
func dropEntry(m map[int]int, k int) {
	delete(m, k)
}

// DropFromNil hands the nil map over, which has no key afterwards.
//
// @Ensures True
func DropFromNil() {
	var m map[int]int
	dropEntry(m, 1)
	// @Assert |m| = 0
}

// AbsentHoldsZero reads the value of the key after it is gone.
//
// @Requires m != nil
// @Modifies m
// @Ensures m'[3] = 0
func AbsentHoldsZero(m map[int]int) {
	dropEntry(m, 3)
}

// AbsentHoldsOne claims another value.
//
// @Requires m != nil
// @Modifies m
// @Ensures m'[3] = 1
func AbsentHoldsOne(m map[int]int) {
	dropEntry(m, 3)
} // want `vego: postcondition may not hold: m'\[3\] = 1`

// bumpTo sets one key and returns what it set.
//
// @Requires m != nil
// @Modifies m[k]
// @Ensures has(m', k) And m'[k] = 1 And r = 1
func bumpTo(m map[int]int, k int) (r int) {
	m[k] = 1
	return 1
}

// ReadBesideCall reads one key beside a call that writes another: Go may
// read it before or after the call, and either gives one value.
//
// @Requires m != nil And a != b And m[a] < 1000
// @Modifies m
// @Ensures True
func ReadBesideCall(m map[int]int, a, b int) {
	x := m[a] + bumpTo(m, b)
	_ = x
}

// ReadBesideCallSameKey may read the key the call writes.
//
// @Requires m != nil And m[a] < 1000
// @Modifies m
// @Ensures True
func ReadBesideCallSameKey(m map[int]int, a, b int) {
	x := m[a] + bumpTo(m, b) // want `vego: m\[a\] may be read before or after the call to bumpTo`
	_ = x
}

func setEntry(m map[string]int, k string, v int) { m[k] = v }

// TrustedEntry keeps another key across a trusted function whose entry
// lists one entry.
//
// @Requires m != nil And m["a"] = 1 And k != "a"
// @Modifies m
// @Ensures m'["a"] = 1 And m'[k] = 2
func TrustedEntry(m map[string]int, k string) {
	setEntry(m, k, 2)
}

// FieldOfEntry names a field of a value held in a map.
//
// @Modifies m[k].qty // want `vego: in Modifies annotation: m\[k\].qty is part of a value that a map holds, which a Modifies clause names only as a whole entry of the map`
// @Ensures True
func FieldOfEntry(m map[string]entry, k string) {}

// AddsCountedSame claims the count is as it was after a key is added.
//
// @Requires a != nil And ~has(a, 1)
// @Modifies a
// @Ensures |a'| = |a|
func AddsCountedSame(a map[int]int) {
	setTwo(a, a, 1, 1)
} // want `vego: postcondition may not hold: \|a'\| = \|a\|`

// GuardedEntry calls on one side of &&: where the call does not run, the
// entry is as it was.
//
// @Requires m != nil
// @Modifies m
// @Ensures ~flag -> (has(m', 3) <-> has(m, 3)) And m'[3] = m[3]
func GuardedEntry(m map[int]int, flag bool) {
	_ = flag && bumpTo(m, 3) == 1
}

// touchEntry may set one key and says nothing of it.
//
// @Modifies m[k]
// @Ensures True
func touchEntry(m map[int]int, k int) {
	if m != nil {
		m[k] = 1
	}
}

// NilStaysEmpty hands the nil map to it: nothing can be put into the nil
// map, so it has no key afterwards.
//
// @Ensures True
func NilStaysEmpty() {
	var m map[int]int
	touchEntry(m, 1)
	// @Assert |m| = 0
}

// NilGetsKey claims the nil map got the key.
//
// @Ensures True
func NilGetsKey() {
	var m map[int]int
	touchEntry(m, 1)
	// @Assert |m| = 1 // want `vego: assertion may not hold: \|m\| = 1`
}
