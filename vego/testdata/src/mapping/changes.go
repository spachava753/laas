package mapping

import (
	"maps"
	"sort"
)

// The programs of a range over a map whose body changes a map of the
// ranged type. Writing a key the map has and deleting a key have one
// meaning; adding a key does not, since Go may or may not visit it.

type nodeset map[string]bool

// AddAll writes every key of x into s, which may be x itself: then each
// write is of a key the map has.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func (s nodeset) AddAll(x nodeset) {
	for node := range x {
		s[node] = true
	}
}

// DropNegative deletes the key of each iteration whose value is negative.
//
// @Requires m != nil
// @Modifies m
// @Ensures Forall k in m' : m'[k] >= 0
func DropNegative(m map[string]int) {
	// @Visited done
	// @Invariant Forall k in m : has(old(m), k) And m[k] = old(m[k])
	// @Invariant Forall k in done : has(m, k) -> m[k] >= 0
	for k, v := range m {
		if v < 0 {
			delete(m, k)
		}
	}
}

// DropNegativeWrong claims that no key is left.
//
// @Requires m != nil
// @Modifies m
// @Ensures |m'| = 0
func DropNegativeWrong(m map[string]int) {
	// @Invariant Forall k in m : has(old(m), k) And m[k] = old(m[k])
	for k, v := range m {
		if v < 0 {
			delete(m, k)
		}
	}
} // want `vego: postcondition may not hold: \|m'\| = 0`

// Clear deletes every key, and counts what is left.
//
// @Requires m != nil
// @Modifies m
// @Ensures |m'| = 0
func Clear(m map[int]int) {
	// @Snapshot n0 = |m|
	// @Visited done
	// @Invariant |m| = n0 - |done| And (Forall k in m : ~has(done, k))
	for k := range m {
		delete(m, k)
	}
}

// Bump adds one to every value. Each write is of a key the map has, and a
// later iteration reads the value as it is then.
//
// @Requires m != nil And (Forall k in m : m[k] < 1000)
// @Modifies m
// @Ensures Forall k in m : m'[k] <= 1000
func Bump(m map[string]int) {
	// @Visited done
	// @Invariant Forall k in m : has(old(m), k)
	// @Invariant Forall k in old(m) : has(m, k)
	// @Invariant Forall k in m : (has(done, k) -> m[k] = old(m[k]) + 1) And (~has(done, k) -> m[k] = old(m[k]))
	for k := range m {
		m[k] = m[k] + 1
	}
}

// AddsKeys adds a key in each iteration.
//
// @Requires m != nil And (Forall k in m : 0 <= k < 100)
// @Modifies m
// @Ensures True
func AddsKeys(m map[int]int) {
	for k := range m {
		if k < 100 {
			m[k+100] = 1 // want `vego: this may add a key to m, the map that the loop at .* ranges over, and Go may or may not visit a key added during the loop; collect the new entries in another map and add them after the loop`
		}
	}
}

// ReAdds deletes the key of the iteration and adds it again, which makes
// it a key added during the loop.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func ReAdds(m map[int]int) {
	for k := range m {
		delete(m, k)
		m[k] = 1 // want `vego: this may add a key to m, the map that the loop at .* ranges over`
	}
}

// AddsThroughLiteral adds a key in a literal bound before the loop.
//
// @Requires m != nil And (Forall k in m : 0 <= k < 100)
// @Modifies m
// @Ensures True
func AddsThroughLiteral(m map[int]int) {
	add := func(x int) {
		m[x] = 1 // want `vego: this may add a key to m, the map that the loop at .* ranges over`
	}
	for k := range m {
		add(k + 100)
	}
}

// AddsThroughHanded adds a key in a literal handed to a trusted function.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func AddsThroughHanded(m map[int]int) {
	for range m {
		_ = sort.Search(10, func(i int) (r bool) {
			m[i+100] = 1 // want `vego: this may add a key to m, the map that the loop at .* ranges over`
			return true
		})
	}
}

// SkipsDeleted deletes, at key 1, the key 2, which the loop may not have
// reached: the loop then visits one key, and the claim that it visits two
// is false.
//
// @Requires m != nil And |m| = 2 And has(m, 1) And has(m, 2)
// @Modifies m
// @Ensures r = 2
func SkipsDeleted(m map[int]int) (r int) {
	del := func(x int) { delete(m, x) }
	// @Visited done
	// @Invariant r = |done|
	for k := range m { // want `vego: loop invariant may not be preserved: r = \|done\|`
		if k == 1 {
			del(2)
		}
		r++
	}
	return r
}

// SkipsDeletedBounded claims only what holds when a position is skipped:
// the visited set counts the positions passed, skipped ones included.
//
// @Requires m != nil And |m| = 2 And has(m, 1) And has(m, 2)
// @Modifies m
// @Ensures r <= 2
func SkipsDeletedBounded(m map[int]int) (r int) {
	del := func(x int) { delete(m, x) }
	// @Visited done
	// @Invariant r <= |done|
	for k := range m {
		if k == 1 {
			del(2)
		}
		r++
	}
	return r
}

// SkipsShadowed deletes through a variable of its own that shadows the key
// of the iteration, so the loop may skip the next key.
//
// @Requires m != nil And |m| = 2 And has(m, 1) And has(m, 2)
// @Requires Forall k in m : 1 <= k <= 2
// @Modifies m
// @Ensures r = 2
func SkipsShadowed(m map[int]int) (r int) {
	// @Visited done
	// @Invariant r = |done| And (Forall k in m : 1 <= k <= 2)
	for k := range m { // want `vego: loop invariant may not be preserved: r = \|done\|`
		k := 3 - k
		delete(m, k)
		r++
	}
	return r
}

// SkipsHanded deletes in a literal handed to a trusted function.
//
// @Requires m != nil And |m| = 2 And has(m, 1) And has(m, 2)
// @Requires Forall k in m : 1 <= k <= 2
// @Modifies m
// @Ensures r = 2
func SkipsHanded(m map[int]int) (r int) {
	// @Visited done
	// @Invariant r = |done|
	for k := range m { // want `vego: loop invariant may not be preserved: r = \|done\|`
		_ = sort.Search(1, func(i int) (found bool) {
			delete(m, 3-k)
			return true
		})
		r++
	}
	return r
}

// CopiesIntoRanged calls maps.Copy into the map the loop ranges over.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func CopiesIntoRanged(m, src map[int]int) {
	for range m {
		maps.Copy(m, src) // want `vego: Copy may modify m while the loop at .* ranges over it, and may add a key, which Go may or may not visit during the loop; change the map in the loop's body, or after the loop`
	}
}

// DeletesFuncOfRanged calls maps.DeleteFunc on the map the loop ranges
// over.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func DeletesFuncOfRanged(m map[int]int) {
	for range m {
		maps.DeleteFunc(m, func(k, v int) (r bool) { return v < 0 }) // want `vego: DeleteFunc may modify m while the loop at .* ranges over it`
	}
}

// CopiesFromRanged copies from the map the loop ranges over into another.
//
// @Requires m != nil And src != nil And m != src
// @Modifies m
// @Ensures True
func CopiesFromRanged(m, src map[int]int) {
	for range src {
		maps.Copy(m, src)
	}
}

// CopiesMaybeRanged may copy into the map it ranges over.
//
// @Requires m != nil And src != nil
// @Modifies m
// @Ensures True
func CopiesMaybeRanged(m, src map[int]int) {
	for range src {
		maps.Copy(m, src) // want `vego: Copy may modify src while the loop at .* ranges over it`
	}
}

type graph map[string]nodeset

// Transpose builds the reverse graph while it ranges over the graph: rev
// is a map of the ranged type, and it is a new one.
//
// @Ensures result != nil
func (g graph) Transpose() (result graph) {
	rev := make(graph)
	for node, edges := range g {
		_ = edges
		rev[node] = nodeset{}
	}
	return rev
}

// AddsToArgument writes another graph of the type, which may be the one
// it ranges over.
//
// @Requires out != nil
// @Modifies out
// @Ensures True
func (g graph) AddsToArgument(out graph) {
	for node := range g {
		_ = node
		out["x"] = nodeset{} // want `vego: this may add a key to g, the map that the loop at .* ranges over`
	}
}

// DeferredAfterLoop returns from inside the loop, which ends it: the
// deferred delete runs after the loop.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func DeferredAfterLoop(m map[int]int) {
	defer func() { delete(m, 7) }()
	for k := range m {
		if k == 1 {
			return
		}
	}
}

// AfterBreak adds a key once the loop is left, which ends the range.
//
// @Requires m != nil
// @Modifies m
// @Ensures has(m', 1000)
func AfterBreak(m map[int]int) {
	for k := range m {
		if k == 1 {
			break
		}
	}
	m[1000] = 1
}

// DeleteThroughAlias deletes the key of each iteration through another
// name for the map.
//
// @Requires m != nil
// @Modifies m
// @Ensures |m'| = 0
func DeleteThroughAlias(m map[int]int) {
	alias := m
	// @Snapshot n0 = |m|
	// @Visited done
	// @Invariant |m| = n0 - |done| And (Forall k in m : ~has(done, k))
	for k := range m {
		delete(alias, k)
	}
}
