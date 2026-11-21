package stdentries

import (
	"cmp"
	"maps"
)

// CloneCounts copies a map of counts.
//
// @Ensures |r| = |m|
func CloneCounts(m map[string]int) (r map[string]int) {
	return maps.Clone(m)
}

// CloneThenWrite writes the copy, which is new.
//
// @Requires m != nil
// @Ensures |r| >= 0
func CloneThenWrite(m map[string]int) (r map[string]int) {
	c := maps.Clone(m)
	c["a"] = 1
	return c
}

// CloneWriteInner writes an inner slice of a shallow copy, which is the
// inner slice of what it was given.
//
// @Requires m != nil
// @Ensures True
func CloneWriteInner(m map[string][]int) {
	c := maps.Clone(m)
	if s := c["a"]; len(s) > 0 {
		s[0] = 1 // want `s\[0\] is assigned, which CloneWriteInner may not modify`
	}
}

// Merge copies one map into another.
//
// @Requires dst != nil
// @Modifies dst
// @Ensures |dst'| >= |src|
func Merge(dst, src map[int]int) {
	maps.Copy(dst, src)
}

// MergeSelf copies a map into itself.
//
// @Requires m != nil
// @Modifies m
// @Ensures |m'| >= |m|
func MergeSelf(m map[int]int) {
	maps.Copy(m, m)
}

// MergeNil may copy into a nil map.
//
// @Modifies dst
// @Ensures True
func MergeNil(dst, src map[int]int) {
	maps.Copy(dst, src) // want `precondition of Copy may not hold: dst != nil Or \|src\| = 0`
}

// MergeUnlisted copies into a map it does not list.
//
// @Requires dst != nil
// @Ensures True
func MergeUnlisted(dst, src map[int]int) {
	maps.Copy(dst, src) // want `Copy may modify dst, which MergeUnlisted may not modify`
}

// DropEmpty deletes the keys with a count of zero.
//
// @Modifies m
// @Ensures |m'| <= |m|
func DropEmpty(m map[string]int) {
	maps.DeleteFunc(m, func(k string, v int) bool { return v == 0 && len(k) > 0 })
}

// DropWrong says that nothing was deleted.
//
// @Modifies m
// @Ensures |m'| = |m|
func DropWrong(m map[string]int) {
	maps.DeleteFunc(m, func(k string, v int) bool { return v == 0 })
} // want `postcondition may not hold: \|m'\| = \|m\|`

// ByName compares two entities by name, as a sorting function does.
//
// @Ensures r = 0 <-> a.Name = b.Name
func ByName(a, b Entity) (r int) {
	return cmp.Compare(a.Name, b.Name)
}

// ByNumber compares two integers.
//
// @Ensures -1 <= r And r <= 1
func ByNumber(a, b int) (r int) {
	return cmp.Compare(a, b)
}

// ByNumberOrder expects an order, which the entry does not say.
//
// @Ensures a < b -> r < 0
func ByNumberOrder(a, b int) (r int) {
	return cmp.Compare(a, b) // want `postcondition may not hold: a < b -> r < 0`
}

// ByWeight compares floats, of which a formula can say nothing.
//
// @Ensures True
func ByWeight(a, b float64) (r int) {
	return cmp.Compare(a, b) // want `cannot be used with T = float64: in its ensures "result = 0 <-> x = y": operator = cannot be applied to float values; a formula can say nothing of a float; write out what it does instead`
}
