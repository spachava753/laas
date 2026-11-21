package mapping

// The programs of quantifiers over the keys of a map: Forall k in m says
// something of every key m has, and Exists k in m of some key it has.

// SumBounded adds up values that are each at most 100, of a map with
// string keys, which no quantifier over the integers can describe.
//
// @Requires Forall k in m : 0 <= m[k] <= 100
// @Ensures 0 <= total <= 100 * |m|
func SumBounded(m map[string]int) (total int) {
	// @Visited done
	// @Invariant 0 <= total <= 100 * |done|
	for _, n := range m {
		total += n
	}
	return total
}

// SumUnbounded has no bound on the values, so the sum may overflow.
//
// @Requires Forall k in m : 0 <= m[k]
// @Ensures 0 <= total
func SumUnbounded(m map[string]int) (total int) {
	// @Invariant 0 <= total
	for _, n := range m {
		total += n // want `vego: addition may overflow int`
	}
	return total
}

// Widened copies a map with string keys into one of wider values, and
// says what the copy holds.
//
// @Ensures |c| = |m| And (Forall k in m : has(c, k)) And (Forall k in c : has(m, k) And c[k] = m[k])
func Widened(m map[string]int32) (c map[string]int64) {
	c = make(map[string]int64)
	// @Visited done
	// @Invariant |c| = |done| And (Forall k in done : has(c, k)) And (Forall k in c : has(done, k) And c[k] = m[k])
	for k, v := range m {
		c[k] = int64(v)
	}
	return c
}

// WidenedOneLess claims a value the copy does not hold.
//
// @Ensures Forall k in c : c[k] = m[k] + 1
func WidenedOneLess(m map[string]int32) (c map[string]int64) {
	c = make(map[string]int64)
	// @Visited done
	// @Invariant |c| = |done| And (Forall k in done : has(c, k)) And (Forall k in c : has(done, k) And c[k] = m[k])
	for k, v := range m {
		c[k] = int64(v)
	}
	return c // want `vego: postcondition may not hold: Forall k in c : c\[k\] = m\[k\] \+ 1`
}

// Found says that some key holds 3, given one that does.
//
// @Requires has(m, "a") And m["a"] = 3
// @Ensures Exists k in m : m[k] = 3
func Found(m map[string]int) {}

// FoundNowhere says the same of any map.
//
// @Ensures Exists k in m : m[k] = 3
func FoundNowhere(m map[string]int) {} // want `vego: postcondition may not hold: Exists k in m : m\[k\] = 3`

// AbsentKeysHoldZero uses a key the map lacks: a quantifier over the keys
// says nothing of it.
//
// @Requires Forall k in m : m[k] = 1
// @Ensures m[0] = 1
func AbsentKeysHoldZero(m map[int]int) {} // want `vego: postcondition may not hold: m\[0\] = 1`

// ShortKeys bounds the length of every key.
//
// @Requires Forall k in m : |k| <= 3
// @Ensures Forall k in m : |k| < 4
func ShortKeys(m map[string]int) {}

// ShorterKeys claims a tighter bound.
//
// @Requires Forall k in m : |k| <= 3
// @Ensures Forall k in m : |k| < 3
func ShorterKeys(m map[string]int) {} // want `vego: postcondition may not hold: Forall k in m : \|k\| < 3`

// LongKey asks for a map whose keys are short and that has a long one.
//
// @Requires (Forall k in m : |k| <= 3) And has(m, "abcd")
// @Ensures True
func LongKey(m map[string]int) {} // want `vego: nothing can satisfy the Requires clauses of LongKey`

// Inner speaks of the keys of the maps held under each key.
//
// @Requires Forall k in g : g[k] != nil And (Forall j in g[k] : g[k][j])
// @Ensures r
func Inner(g map[string]map[string]bool, a, b string) (r bool) {
	if inner, ok := g[a]; ok {
		if _, ok := inner[b]; ok {
			return inner[b]
		}
	}
	return true
}

// Kept says that every key on entry is still there.
//
// @Requires m != nil
// @Modifies m
// @Ensures Forall k in m : has(m', k)
func Kept(m map[string]int, k string) {
	m[k] = 1
}

// KeptWrong may delete one.
//
// @Requires m != nil
// @Modifies m
// @Ensures Forall k in m : has(m', k)
func KeptWrong(m map[string]int, k string) {
	delete(m, k)
} // want `vego: postcondition may not hold: Forall k in m : has\(m', k\)`

type edgeSet map[string]bool
type edgeGraph map[string]edgeSet

// addNode keeps every other key of the graph, which a contract says of a
// map of references with a quantifier, since Modifies cannot name the entry
// of one alone.
//
// @Requires g != nil
// @Modifies g
// @Ensures edges != nil And has(g', node) And g'[node] = edges
// @Ensures Forall k in g : has(g', k) And (k = node Or g'[k] = g[k])
func (g edgeGraph) addNode(node string) (edges edgeSet) {
	edges = g[node]
	if edges == nil {
		edges = make(edgeSet)
		g[node] = edges
	}
	return edges
}

// addNodeKeepsAll claims that no value changes, also that of node.
//
// @Requires g != nil
// @Modifies g
// @Ensures Forall k in g : has(g', k) And g'[k] = g[k]
func (g edgeGraph) addNodeKeepsAll(node string) (edges edgeSet) {
	edges = g[node]
	if edges == nil {
		edges = make(edgeSet)
		g[node] = edges
	}
	return edges // want `vego: postcondition may not hold: Forall k in g : has\(g', k\) And g'\[k\] = g\[k\]`
}

// addNodeKeepsNode excepts every key but node.
//
// @Requires g != nil
// @Modifies g
// @Ensures Forall k in g : has(g', k) And (k != node Or g'[k] = g[k])
func (g edgeGraph) addNodeKeepsNode(node string) (edges edgeSet) {
	edges = g[node]
	if edges == nil {
		edges = make(edgeSet)
		g[node] = edges
	}
	return edges // want `vego: postcondition may not hold: Forall k in g : has\(g', k\) And \(k != node Or g'\[k\] = g\[k\]\)`
}

// DeleteOthersKept deletes one key and keeps the others.
//
// @Modifies m
// @Ensures Forall k in m : has(m', k) Or k = key
func DeleteOthersKept(m map[string]int, key string) {
	delete(m, key)
}

// DeleteOthersKeptWrong claims the deleted key is the one kept.
//
// @Modifies m
// @Ensures Forall k in m : has(m', k) Or k != key
func DeleteOthersKeptWrong(m map[string]int, key string) {
	delete(m, key)
} // want `vego: postcondition may not hold: Forall k in m : has\(m', k\) Or k != key`

// DeleteOne leaves no key equal to the one deleted.
//
// @Modifies m
// @Ensures Forall k in m' : k != key
func DeleteOne(m map[string]int, key string) {
	delete(m, key)
}

// SetOne claims the same after setting the key.
//
// @Requires m != nil
// @Modifies m
// @Ensures Forall k in m' : k != key
func SetOne(m map[string]int, key string) {
	m[key] = 0
} // want `vego: postcondition may not hold: Forall k in m' : k != key`
