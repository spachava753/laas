package guide

// The programs of the sections on labelled break and continue and on
// fallthrough.

// @Requires |a| <= 100
// @Ensures found -> 0 <= fi < |a| And 0 <= fj < |a[fi]| And a[fi][fj] = x
// @Ensures ~found -> Forall k in [0, |a|) : Forall m in [0, |a[k]|) : a[k][m] != x
func FindCell(a [][]int, x int) (fi, fj int, found bool) {
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

// @Requires 0 <= n <= 100
// @Ensures True
func SkipsTail(n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
outer:
	for i := 0; i < n; { // want `vego: loop variant may not decrease: n - i`
		for j := range 2 {
			if j == 1 {
				continue outer
			}
		}
		i++
	}
}

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
