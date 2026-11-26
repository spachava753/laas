// Package labels leaves nested loops with labelled break and continue, and
// runs the next clause of a switch with fallthrough, as ordinary code does.
package labels

// Find returns where x is in a, leaving both loops when it finds it.
//
// @Requires |a| <= 100
// @Ensures found -> 0 <= fi < |a| And 0 <= fj < |a[fi]| And a[fi][fj] = x
// @Ensures ~found -> Forall k in [0, |a|) : Forall m in [0, |a[k]|) : a[k][m] != x
func Find(a [][]int, x int) (fi, fj int, found bool) {
	// @Invariant ~found
	// @Invariant Forall k in [0, i) : Forall m in [0, |a[k]|) : a[k][m] != x
outer:
	for i := range a {
		// @Invariant ~found
		// @Invariant Forall m in [0, j) : a[i][m] != x
		for j := range a[i] {
			if a[i][j] == x {
				fi, fj, found = i, j, true
				break outer
			}
		}
	}
	return fi, fj, found
}

// RowsWithNegative counts the rows that hold a negative number, going on
// to the next row at the first one.
//
// @Requires |a| <= 100
// @Ensures 0 <= n <= |a|
func RowsWithNegative(a [][]int) (n int) {
	// @Invariant 0 <= n <= i
outer:
	for i := range a {
		// @Invariant 0 <= n <= i
		for j := range a[i] {
			if a[i][j] < 0 {
				n++
				continue outer
			}
		}
	}
	return n
}

// Counted runs n iterations of a for loop whose post statement runs at
// continue outer too, so its variant decreases there.
//
// @Requires 0 <= n <= 100
// @Ensures r = n
func Counted(n int) (r int) {
	// @Invariant 0 <= i <= n And r = i
	// @Variant n - i
outer:
	for i := 0; i < n; i++ {
		r++
		// @Invariant 0 <= j <= 3
		// @Variant 3 - j
		for j := 0; j < 3; j++ {
			if j == 1 {
				continue outer
			}
		}
	}
	return r
}

// FirstZero leaves the loop from a switch inside it.
//
// @Ensures k = -1 Or (0 <= k < |xs| And xs[k] = 0)
func FirstZero(xs []int) (k int) {
	k = -1
	// @Invariant k = -1
loop:
	for i := range xs {
		switch {
		case xs[i] == 0:
			k = i
			break loop
		}
	}
	return k
}

// Sign leaves a labelled switch from inside a loop in one of its clauses.
//
// @Ensures r = 0 Or r = 1
func Sign(xs []int, positive bool) (r int) {
sw:
	switch {
	case positive:
		// @Invariant r = 0
		for i := range xs {
			if xs[i] > 0 {
				r = 1
				break sw
			}
		}
	}
	return r
}

// Inner names the inner loop, which continue inner goes on with.
//
// @Requires |a| <= 100
// @Ensures 0 <= n
func Inner(a [][]int) (n int) {
	// @Invariant 0 <= n
	for i := range a {
		// @Invariant 0 <= n
	inner:
		for j := range a[i] {
			if a[i][j] == 0 {
				continue inner
			}
			if n < 1000 {
				n++
			}
		}
	}
	return n
}

// Keys goes on to the next key of a map from a loop inside.
//
// @Requires |m| <= 100
// @Ensures 0 <= n <= |m|
func Keys(m map[string][]int) (n int) {
	// @Visited seen
	// @Invariant 0 <= n <= |seen|
outer:
	for k := range m {
		// @Invariant 0 <= n <= |seen|
		for _, x := range m[k] {
			if x < 0 {
				n++
				continue outer
			}
		}
	}
	return n
}

// Fall runs the clause after case 0 too.
//
// @Ensures n = 0 -> r = 2
// @Ensures n = 1 -> r = 1
// @Ensures n != 0 And n != 1 -> r = 10
func Fall(n int) (r int) {
	switch n {
	case 0:
		r = 1
		fallthrough
	case 1:
		r = r + 1
	default:
		r = 10
	}
	return r
}

// FallIntoDefault goes from a case into default, which stands in the
// middle; the clause after default is the one fallthrough skips (F8 of the
// design review).
//
// @Ensures a -> x = 2
// @Ensures ~a And b -> x = 3
// @Ensures ~a And ~b -> x = 2
func FallIntoDefault(a, b bool) (x int) {
	switch {
	case a:
		x = 1
		fallthrough
	default:
		x = 2
	case b:
		x = 3
	}
	return x
}

// FallThenBreak breaks out of the switch in the clause it fell into.
//
// @Ensures n = 0 -> r = 1
func FallThenBreak(n int) (r int) {
	switch n {
	case 0:
		r = 1
		fallthrough
	case 1:
		if r == 1 {
			break
		}
		r = 5
	}
	return r
}

// InnerMap goes on to the next key of the outer map from a range over an
// inner map, whose range ends with the jump.
//
// @Requires |m| <= 100
// @Ensures 0 <= n <= |m|
func InnerMap(m map[string]map[string]int) (n int) {
	// @Visited seen
	// @Invariant 0 <= n <= |seen|
outer:
	for k := range m {
		// @Invariant 0 <= n <= |seen|
		for j := range m[k] {
			if m[k][j] < 0 {
				n++
				continue outer
			}
		}
	}
	return n
}

// BreakThenWrite leaves a range over m from inside it with break outer, and
// then adds a key to m, which no loop ranges over any longer.
//
// @Requires m != nil And |m| < 1000
// @Modifies m
// @Ensures True
func BreakThenWrite(m map[string]int, xs []int) {
outer:
	for i := range xs {
		for k := range m {
			if m[k] == xs[i] {
				break outer
			}
		}
	}
	m["x"] = 1
}

// PerIteration keeps a pointer to the variable of the first iteration
// across continue outer, which ends the iteration and makes a variable for
// the next one: the pointer keeps the first one's value (F9 of the design
// review).
//
// @Ensures r = 0
func PerIteration() (r int) {
	var first *int
	// @Invariant 0 <= i <= 2
	// @Invariant i >= 1 -> first != nil And *first = 0
	// @Variant 2 - i
outer:
	for i := 0; i < 2; i++ {
		if i == 0 {
			first = &i
		}
		// @Invariant 0 <= i < 2 And first != nil And *first = 0
		// @Variant 1 - j
		for j := 0; j < 1; j++ {
			continue outer
		}
	}
	if first == nil {
		return -1
	}
	return *first
}
