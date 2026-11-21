package guide

import "maps"

// The programs of the section Maps of docs/verification.md, after the
// first ones, which are in guide.go.

// KeysOf returns the keys of a map in a slice.
//
// @Ensures |result| = |m|
func KeysOf(m map[string]int) (result []string) {
	result = make([]string, len(m))
	i := 0
	// @Visited done
	// @Invariant i = |done|
	for k := range m {
		result[i] = k
		i++
	}
	return result
}

// KeysOfUncounted has no invariant that ties i to the iterations.
//
// @Ensures True
func KeysOfUncounted(m map[string]int) (result []string) {
	result = make([]string, len(m))
	i := 0
	// @Invariant 0 <= i
	for k := range m {
		result[i] = k // want `vego: index may be out of range`
		i++
	}
	return result
}

// SumScores adds up the values of a map whose values are each at most 100.
//
// @Requires Forall k in m : 0 <= m[k] <= 100
// @Ensures 0 <= total <= 100 * |m|
func SumScores(m map[string]int) (total int) {
	// @Visited done
	// @Invariant 0 <= total <= 100 * |done|
	for _, n := range m {
		total += n
	}
	return total
}

// Widen copies a map into one with wider values.
//
// @Ensures |c| = |m| And (Forall k in m : has(c, k) And c[k] = m[k])
func Widen(m map[string]int32) (c map[string]int64) {
	c = make(map[string]int64)
	// @Visited done
	// @Invariant |c| = |done| And (Forall k in done : has(c, k) And c[k] = m[k])
	// @Invariant Forall k in c : has(done, k)
	for k, v := range m {
		c[k] = int64(v)
	}
	return c
}

// DropNegative deletes the keys whose values are negative.
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

// CountDeleting deletes a key the loop may not have reached yet.
//
// @Requires m != nil And has(m, "a") And has(m, "b")
// @Modifies m
// @Ensures n = |m|
func CountDeleting(m map[string]int) (n int) {
	// @Visited done
	// @Invariant n = |done|
	for k := range m { // want `vego: loop invariant may not be preserved: n = \|done\|`
		if k == "a" {
			delete(m, "b")
		}
		n++
	}
	return n
}

// CountDeletingAtMost says only what holds when a key is skipped.
//
// @Requires m != nil And has(m, "a") And has(m, "b")
// @Modifies m
// @Ensures n <= |m|
func CountDeletingAtMost(m map[string]int) (n int) {
	// @Visited done
	// @Invariant n <= |done|
	for k := range m {
		if k == "a" {
			delete(m, "b")
		}
		n++
	}
	return n
}

// Hit counts one visit to a page.
//
// @Requires counts != nil And counts[page] < 1000000
// @Modifies counts[page]
// @Ensures has(counts', page) And counts'[page] = counts[page] + 1
func Hit(counts map[string]int, page string) {
	counts[page]++
}

// HitTwice counts two visits, and keeps what it knew of another page.
//
// @Requires counts != nil And counts["a"] < 1000 And counts["home"] = 7
// @Modifies counts
// @Ensures counts'["a"] = counts["a"] + 2 And counts'["home"] = 7
func HitTwice(counts map[string]int) {
	Hit(counts, "a")
	Hit(counts, "a")
}

// AddTag appends to the slice a map holds under a key.
//
// @Requires tags != nil And |tags[k]| < 1000
// @Modifies tags[k]
// @Ensures True
func AddTag(tags map[string][]string, k, tag string) {
	tags[k] = append(tags[k], tag) // want `vego: tags\[k\] is assigned, which AddTag may not modify; list the whole map in a // @Modifies clause: an entry of a map whose values are pointers, slices, maps, or interface values is covered only by the map, since a path such as m\[k\] in a Modifies clause names what the value refers to`
}

// Group adds a set for a key unless one is there, and keeps the sets of
// every other key.
//
// @Requires g != nil
// @Modifies g
// @Ensures set != nil And has(g', k) And g'[k] = set
// @Ensures Forall j in g : has(g', j) And (j = k Or g'[j] = g[j])
func Group(g map[string]map[string]bool, k string) (set map[string]bool) {
	set = g[k]
	if set == nil {
		set = make(map[string]bool)
		g[k] = set
	}
	return set
}

// TwoKeys has two keys, which is not proved to make a count of two.
//
// @Requires has(m, "a") And has(m, "b")
// @Ensures |m| >= 2
func TwoKeys(m map[string]int) {} // want `vego: postcondition may not hold: \|m\| >= 2`

// MergeEach copies src into the map it ranges over.
//
// @Requires m != nil
// @Modifies m
func MergeEach(m, src map[string]int) {
	for range m {
		maps.Copy(m, src) // want `vego: Copy may modify m while the loop at maps.go:169:2 ranges over it, and may add a key, which Go may or may not visit during the loop; change the map in the loop's body, or after the loop`
	}
}
