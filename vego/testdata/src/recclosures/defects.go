package recclosures

import "os"

// Endless never marks what it visits, so on a cycle it never ends.
//
// @Ensures True
func (g graph) Endless(roots nodeset) {
	seen := make(nodeset)
	var visit func(node string)
	// @Requires seen != nil And Forall k in g : g[k] != seen
	// @Modifies seen
	// @Variant |g \ seen|
	visit = func(node string) {
		_ = seen[node]
		for e := range g[node] {
			visit(e) // want `variant may not decrease in recursive call: \|g \\ seen\|`
		}
	}
	for root := range roots {
		visit(root)
	}
}

// Unmeasured has no Variant.
//
// @Ensures True
func Unmeasured() {
	var f func(k int)
	// @Requires k >= 0
	f = func(k int) {
		if k > 0 {
			f(k - 1) // want `recursive call needs a // @Variant annotation above the assignment f = func\.\.\. to prove termination`
		}
	}
	f(3)
}

// Wrong claims less than the closure counts.
//
// @Requires 0 <= n <= 1000
// @Ensures r = 0
func Wrong(n int) (r int) {
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
	return c // want `postcondition may not hold: r = 0`
}

// OnPath divides by a variable whose value differs by path: the closure is
// verified with nothing known of it (F6 of the design review).
//
// @Ensures True
func OnPath(k int) (r int) {
	if k > 0 {
		r = 1
	}
	var div func(n int) (q int)
	// @Requires 0 <= n
	// @Ensures True
	div = func(n int) (q int) {
		return n / k // want `division by zero`
	}
	return div(10)
}

// Forgotten relies on a variable after a loop that calls the closure
// assigning it (F8).
//
// @Ensures True
func Forgotten() {
	n := 0
	var inc func()
	// @Requires n < 100
	// @Modifies n
	// @Ensures n' = n + 1
	inc = func() {
		n++
	}
	// @Invariant 0 <= i <= 3 And n <= i
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		inc()
	}
	// @Assert n = 0 // want `assertion may not hold: n = 0`
	_ = n
}

// Unlisted assigns a captured variable that its Modifies does not list.
//
// @Ensures True
func Unlisted() {
	count := 0
	var f func(k int)
	// @Requires 0 <= k <= 3 And 0 <= count And count + k <= 10
	// @Variant k
	f = func(k int) {
		if k > 0 {
			count++ // want `count is assigned, which the closure f may not modify; list it in a // @Modifies clause above f = func\.\.\.`
			f(k - 1)
		}
	}
	f(2)
}

// Empty has no contract above its assignment, which is the empty one.
//
// @Ensures True
func Empty() {
	count := 0
	var f func()
	f = func() {
		if count < 10 {
			count++ // want `count is assigned, which the closure f may not modify`
		}
	}
	f()
}

// CappedAppend appends to a captured slice in place, over memory the
// function holds through another slice.
//
// @Ensures True
func CappedAppend() {
	s := make([]int, 0, 4)
	t := s[:cap(s)]
	var push func(k int)
	// @Requires 0 <= k <= 2 And |s| + k <= 2
	// @Modifies s
	// @Variant k
	push = func(k int) {
		if k > 0 {
			s = append(s, k)
			push(k - 1)
		}
	}
	push(2)
	// @Assert t[0] = 0 // want `assertion may not hold: t\[0\] = 0`
	_ = t
}

// Exits ends the process in a recursive closure (F9).
//
// @Ensures True
func Exits() {
	var f func()
	// @Ensures True
	f = func() {
		os.Exit(1) // want `cannot verify the closure f: it calls os.Exit, which may end the process, in the closure f; a recursive closure may not end the process yet`
	}
	f()
}

// Rotate never ends: each call drops its key from a and adds the next, so
// a gains a key while |a \ s| stays one. Only (i) refuses it: a may not
// gain a key.
//
// @Requires a != nil And s != nil And 0 <= k < 3 And has(a, k)
// @Requires Forall j in [0, 3) : ~has(s, j)
// @Modifies a
// @Ensures True
func Rotate(a, s map[int]bool, k int) {
	var turn func(k int)
	// @Requires 0 <= k < 3 And has(a, k)
	// @Requires Forall j in [0, 3) : ~has(s, j)
	// @Modifies a
	// @Variant |a \ s|
	turn = func(k int) {
		m := (k + 1) % 3
		delete(a, k)
		a[m] = true
		turn(m) // want `variant may not decrease in recursive call: \|a \\ s\|`
	}
	turn(k)
}

// Swap never ends: each call marks its key and unmarks the other, so
// |a \ s| stays one. Only (ii) refuses it: s may not lose a key of a.
//
// @Requires a != nil And s != nil And 0 <= k <= 1 And has(a, 0) And has(a, 1)
// @Requires ~has(s, k) And has(s, 1 - k)
// @Modifies s
// @Ensures True
func Swap(a, s map[int]bool, k int) {
	var flip func(k int)
	// @Requires 0 <= k <= 1 And has(a, 0) And has(a, 1)
	// @Requires ~has(s, k) And has(s, 1 - k)
	// @Modifies s
	// @Variant |a \ s|
	flip = func(k int) {
		s[k] = true
		delete(s, 1-k)
		flip(1 - k) // want `variant may not decrease in recursive call: \|a \\ s\|`
	}
	flip(k)
}

// Stay never ends and marks nothing new: its key is seen already. Only
// the condition of (iii) that the key was not seen before refuses it.
//
// @Requires a != nil And s != nil And has(a, k) And has(s, k)
// @Ensures True
func Stay(a, s map[int]bool, k int) {
	var stay func(k int)
	// @Requires has(a, k) And has(s, k)
	// @Variant |a \ s|
	stay = func(k int) {
		stay(k) // want `variant may not decrease in recursive call: \|a \\ s\|`
	}
	stay(k)
}
