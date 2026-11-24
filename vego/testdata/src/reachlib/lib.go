// Package reachlib has a counter that code of another package changes
// while a call through a value runs (F20 of the review of step 3 of
// package-level variables).
package reachlib

// Count counts.
var Count int

// Inc counts, and is not verified.
func Inc() { Count++ }

// IncV counts.
//
// @Modifies Count
// @Ensures True
func IncV() {
	if Count < 1000 {
		Count++
	}
}
