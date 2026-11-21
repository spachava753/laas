// Package deletes calls the shipped entries of slices.Delete,
// slices.DeleteFunc, and slices.Compact, whose checks for a contradiction
// must conclude; see TestAnalyzer.
package deletes

import "slices"

// @Requires 0 <= i < |s|
// @Modifies s
// @Ensures |r| = |s| - 1
func Drop(s []int, i int) (r []int) {
	return slices.Delete(s, i, i+1)
}

// The result is shorter by one, not by none.
// @Requires 0 <= i < |s|
// @Modifies s
// @Ensures |r| = |s|
func DropWrong(s []int, i int) (r []int) {
	return slices.Delete(s, i, i+1) // want `postcondition may not hold: \|r\| = \|s\|`
}

// @Modifies s
// @Ensures |r| <= |s|
func DropNegative(s []int) (r []int) {
	return slices.DeleteFunc(s, negative)
}

// @Ensures True
func negative(x int) (r bool) {
	return x < 0
}

// @Modifies s
// @Ensures |r| <= |s|
func Dedup(s []int) (r []int) {
	return slices.Compact(s)
}
