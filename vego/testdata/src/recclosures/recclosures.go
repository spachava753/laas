// Package recclosures holds recursive local closures that verify: a
// depth-first search over a map of sets, a count, and the ways the function
// around a closure and the closure share variables.
package recclosures

import "strings"

type nodeset map[string]bool
type graph map[string]nodeset

// ReachableFrom is the depth-first search of x/tools' digraph. What is
// left to visit is the set of nodes of g not yet seen.
//
// @Ensures result != nil And fresh(result)
func (g graph) ReachableFrom(roots nodeset) (result nodeset) {
	seen := make(nodeset)
	var visit func(node string)
	// @Requires seen != nil And Forall k in g : g[k] != seen
	// @Requires Forall k in seen : seen[k]
	// @Modifies seen
	// @Variant |g \ seen|
	// @Ensures Forall k in seen : has(seen', k)
	// @Ensures Forall k in seen' : seen'[k]
	visit = func(node string) {
		if !seen[node] {
			seen[node] = true
			// @Invariant has(seen, node) And Forall k in old(seen) : has(seen, k)
			// @Invariant Forall k in seen : seen[k]
			for e := range g[node] {
				visit(e)
			}
		}
	}
	// @Invariant Forall k in seen : seen[k]
	for root := range roots {
		visit(root)
	}
	return seen
}

// Count counts down through a closure that assigns a variable of the
// function around it.
//
// @Requires 0 <= n <= 1000
// @Ensures r = n
func Count(n int) (r int) {
	c := 0
	var down func(k int)
	// @Requires 0 <= k And 0 <= c And c + k <= 1000
	// @Modifies c
	// @Variant k
	// @Ensures c' = c + k
	down = func(k int) {
		if k > 0 {
			c++
			down(k - 1)
		}
	}
	down(n)
	return c
}

// Between reads, between two calls, a variable the closure assigns, and
// assigns one the closure reads.
//
// @Ensures r = 7
func Between() (r int) {
	c, step := 0, 1
	var add func(k int)
	// @Requires 0 <= k <= 3 And 0 <= c And c + 2 * k <= 100 And 0 <= step <= 2
	// @Modifies c
	// @Variant k
	// @Ensures c' = c + k * step
	add = func(k int) {
		if k > 0 {
			c += step
			add(k - 1)
		}
	}
	add(3)
	// @Assert c = 3
	step = 2
	add(2)
	return c
}

// Looped calls a closure in a loop, which forgets what it assigns but for
// what the invariant keeps.
//
// @Ensures r = 6
func Looped() (r int) {
	c := 0
	var inc func()
	// @Requires 0 <= c <= 100
	// @Modifies c
	// @Ensures c' = c + 1
	inc = func() {
		c++
	}
	// @Invariant 0 <= i <= 3 And c = 2 * i
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		inc()
		inc()
	}
	return c
}

// Appended grows a slice it captures; the function sees the new slice.
//
// @Ensures |r| = 3
func Appended() (r []int) {
	var s []int
	var push func(k int)
	// @Requires 0 <= k <= 3 And |s| + k <= 10
	// @Modifies s
	// @Variant k
	// @Ensures |s'| = |s| + k
	push = func(k int) {
		if k > 0 {
			s = append(s, k)
			push(k - 1)
		}
	}
	push(3)
	return s
}

// Ranged makes a closure in each iteration of a range loop, over the
// iteration's own variable.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 10
// @Ensures True
func Ranged(xs []int) {
	for _, x := range xs {
		var down func(k int)
		// @Requires 0 <= k <= 10
		// @Variant k
		down = func(k int) {
			if k > 0 && x >= 0 {
				down(k - 1)
			}
		}
		down(x)
	}
}

// FromHanded calls a closure from a literal handed to strings.IndexFunc,
// which may run it any number of times.
//
// @Ensures True
func FromHanded(line string) (n int) {
	count := 0
	var bump func()
	// @Requires count < 1000000
	// @Modifies count
	bump = func() {
		if count < 1000000 {
			count++
		}
	}
	_ = strings.IndexFunc(line, func(r rune) bool {
		if count < 1000000 {
			bump()
		}
		return false
	})
	return count
}

// GuardedTrue is Guarded with a contract that holds: c is one where the
// call ran (F17).
//
// @Ensures x <= 0 -> r = 0
func GuardedTrue(x int) (r int) {
	c := 0
	var bump func() (ok bool)
	// @Requires 0 <= c <= 10
	// @Modifies c
	// @Ensures c' = c + 1 And ok
	bump = func() (ok bool) {
		c++
		return true
	}
	if x > 0 && bump() {
	}
	return c
}
