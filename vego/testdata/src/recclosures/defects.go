package recclosures

import (
	"os"
	"strings"
)

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

// Counter has a method with a pointer receiver.
type Counter struct{ n int }

// @Requires c != nil And c.n < 100
// @Modifies c
// @Ensures True
func (c *Counter) Inc() { c.n++ }

// ByMethod captures a variable whose method with a pointer receiver takes
// its address (F7).
//
// @Ensures True
func ByMethod() {
	var c Counter
	var f func()
	// @Ensures True
	f = func() { // want `cannot verify ByMethod: the closure f captures c, whose address is taken in ByMethod`
		if c.n < 100 {
			c.Inc()
		}
	}
	f()
}

// BySlice captures an array that the function slices (F7).
//
// @Ensures True
func BySlice() {
	var a [4]byte
	s := a[:]
	var f func()
	// @Ensures True
	f = func() { // want `cannot verify BySlice: the closure f captures a, whose address is taken in BySlice`
		_ = a[0]
	}
	f()
	_ = s
}

// RunThenAssert relies on a variable after a run of a trusted function
// calls the closure that assigns it (F8).
//
// @Ensures True
func RunThenAssert(line string) {
	n := 0
	var bump func()
	// @Requires n < 1000000
	// @Modifies n
	bump = func() {
		n++
	}
	_ = strings.IndexFunc(line, func(r rune) bool {
		if n < 1000000 {
			bump()
		}
		return false
	})
	// @Assert n = 0 // want `assertion may not hold: n = 0`
	_ = n
}

// Guarded calls the closure on the right of && only: where the call does
// not run, c keeps its value, and where it runs, the Ensures gives the new
// one (F17 of the review of step 1).
//
// @Ensures r = 0
func Guarded(x int) (r int) {
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
	return c // want `postcondition may not hold: r = 0`
}

// DeferredCall calls, in a literal deferred where it is written, a closure
// that assigns the named result after the return (F18).
//
// @Ensures r = 5
func DeferredCall() (r int) {
	var bump func()
	// @Requires 0 <= r <= 10
	// @Modifies r
	// @Ensures r' = r + 1
	bump = func() {
		r++
	}
	defer func() { bump() }()
	return 5 // want `postcondition may not hold: r = 5`
}

// InPlace declares a closure inside a literal called where it is written,
// which assigns a variable of the function (F18).
//
// @Ensures r = 0
func InPlace() (r int) {
	func() {
		var bump func()
		// @Requires 0 <= r <= 10
		// @Modifies r
		// @Ensures r' = r + 1
		bump = func() {
			r++
		}
		bump()
	}()
	return r // want `postcondition may not hold: r = 0`
}

// ViaBound calls, in a closure, a literal bound in the function around
// it, which assigns a variable the closure cannot see change (F19).
//
// @Ensures True
func ViaBound() {
	count := 0
	check := func() {
		if count < 10 {
			count++
		}
	}
	var visit func()
	// @Ensures True
	visit = func() {
		check() // want `cannot verify ViaBound: the closure visit calls check, a function literal bound in ViaBound, which a recursive closure cannot call yet`
	}
	visit()
	check()
}
