// Package readerbad hands the memory of a group to callees that return it
// (F34 of the review of step 2 of part 2 of package-level variables).
package readerbad

import "slices"

// @Invariant Forall i in [0, |items|) : items[i] >= 0 // want `^vego: the invariant of items cannot be relied on: the use of items at r.go:29 lets a reference to what it refers to out of it, so a write through another reference could break the invariant without naming the variable$`
var items = []int{1, 2, 3}

// grow makes items assigned.
//
// @Modifies items
// @Ensures True
func grow() { items = []int{4} }

// same returns what it is handed.
//
// @Ensures r = s
func same(s []int) (r []int) { return s }

// Holder holds a slice.
type Holder struct{ s []int }

// stash keeps what same returns of items.
//
// @Requires h != nil
// @Modifies h
// @Ensures True
func stash(h *Holder) { h.s = same(items) }

// stashClip keeps what slices.Clip returns of items.
//
// @Requires h != nil
// @Modifies h
// @Ensures True
func stashClip(h *Holder) { h.s = slices.Clip(items) }

// poke writes through the alias.
//
// @Requires h != nil And |h.s| > 0
// @Modifies h.s
// @Ensures True
func poke(h *Holder) { h.s[0] = -1 }
