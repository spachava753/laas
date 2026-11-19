package closures

import "fmt"

// Overflows adds in a literal without a bound.
//
// @Ensures True
func Overflows(x int) (result int) {
	return func() int { return x + 1 }() // want `vego: addition may overflow int, in the function literal called at defects.go:9:9`
}

// OutOfRange indexes in a literal at a call where the index may be out of
// range.
//
// @Requires |A| >= 1
// @Ensures True
func OutOfRange(A []int) (result int) {
	at := func(i int) int { return A[i] } // want `vego: index may be out of range, in the function literal called at defects.go:19:9`
	return at(1)
}

// Unguarded calls the literal where its index may be out of range.
//
// @Ensures True
func Unguarded(A []int, i int) (result bool) {
	positive := func(k int) bool { return A[k] > 0 } // want `vego: index may be out of range, in the function literal called at defects.go:27:23`
	return i < len(A) || positive(i)
}

// WritesUnlisted writes memory its Modifies clause does not list.
//
// @Requires |A| >= 1
// @Ensures True
func WritesUnlisted(A []int) {
	func() { A[0] = 1 }() // want `vego: A\[0\] is assigned, which WritesUnlisted may not modify; list it in a // @Modifies clause, in the function literal called at defects.go:35:2`
}

// WrongResult claims what the literal does not do.
//
// @Requires 0 <= x < 100
// @Ensures result = x
func WrongResult(x int) (result int) {
	inc := func(n int) int { return n + 1 }
	return inc(x) // want `vego: postcondition may not hold: result = x`
}

// Twice asserts in a literal what holds at its first call only.
//
// @Ensures True
func Twice() {
	x := 0
	check := func(n int) {
		// @Assert n = 0 // want `vego: assertion may not hold: n = 0, in the function literal called at defects.go:56:2`
	}
	check(x)
	check(x + 1)
}

// ForgetsInLoop calls in a loop a literal that writes memory, and then
// relies on what the loop may have changed.
//
// @Requires |A| >= 1 And n >= 0
// @Modifies A
// @Ensures A'[0] = 0
func ForgetsInLoop(A []int, n int) {
	A[0] = 0
	set := func(i int) { A[i%len(A)] = i }
	// @Invariant 0 <= i <= n
	for i := range n {
		set(i)
	}
} // want `vego: postcondition may not hold: A'\[0\] = 0`

// ShadowsOld names a parameter in old() where a parameter of the literal
// hides it.
//
// @Requires 0 <= n < 100
// @Ensures result = n
func ShadowsOld(n int) (result int) {
	id := func(n int) int {
		// @Assert n = old(n) // want `vego: in Assert annotation: old\(n\): n here is not the parameter of ShadowsOld but a variable that hides it; rename the variable`
		return n
	}
	return id(n)
}

// WrapsUnknown formats, through a literal, an error it was given.
//
// @Ensures True
func WrapsUnknown(e error) (result bool) {
	wrap := func(x error) error { return fmt.Errorf("w: %w", x) } // want `vego: cannot verify WrapsUnknown: formatting x would run the methods of an error whose origin is not known`
	return wrap(e) != nil
}

// Passed hands a literal to another function.
//
// @Ensures True
func Passed() {
	apply(func() {}) // want `vego: cannot verify Passed: a function literal is supported only where it is called or deferred, or as the value that declares a new variable which is only ever called; this one is used as a value`
}

func apply(f func()) { f() }

// Reassigned gives the variable another literal.
//
// @Ensures True
func Reassigned() {
	f := func() {}
	f = func() {} // want `vego: cannot verify Reassigned: f holds a function literal and is used here other than by calling it`
	f()
}

// Compared compares the variable with nil.
//
// @Ensures True
func Compared() (result bool) {
	f := func() {}
	return f != nil // want `vego: cannot verify Compared: f holds a function literal and is used here other than by calling it`
}

// Variadic takes any number of arguments.
//
// @Ensures True
func Variadic() {
	func(xs ...int) {}(1, 2) // want `vego: cannot verify Variadic: variadic function literals are not supported yet`
}

// Recovers calls recover.
//
// @Ensures True
func Recovers() {
	func() {
		recover() // want `vego: cannot verify Recovers: recover is not supported`
	}()
}

// AssignsCaptured changes a variable of the function from a literal.
//
// @Ensures True
func AssignsCaptured() (result int) {
	n := 0
	func() {
		n = 1 // want `vego: cannot verify AssignsCaptured: the function literal assigns n, a variable of the function around it, which is not supported yet`
	}()
	return n
}

// ReadsBeforeOrAfter reads a field that the literal changes, in the same
// expression.
//
// @Requires g != nil And 0 <= g.v < 100
// @Modifies g.v
func ReadsBeforeOrAfter(g *Gauge) (result int) {
	bump := func() int {
		g.Set(g.v + 1)
		return 0
	}
	return g.v + bump() // want `vego: g.v may be read before or after the call to bump, which may change it, and Go does not fix the order`
}

// WrongBranch claims of a literal with two ends what only one gives.
//
// @Requires MinInt < a
// @Ensures result = a
func WrongBranch(a int) (result int) {
	abs := func(n int) int {
		if n < 0 {
			return -n
		}
		return n
	}
	return abs(a) // want `vego: postcondition may not hold: result = a`
}

// GuardSkips claims the effect of a literal called on the right of &&,
// which does not run when c is false.
//
// @Requires |A| >= 1
// @Modifies A
// @Ensures A'[0] = 5
func GuardSkips(A []int, c bool) {
	if c && func() bool { A[0] = 5; return true }() {
		return
	}
} // want `vego: postcondition may not hold: A'\[0\] = 5`

// WrongLast claims of a literal with two ends what only its first end
// gives; with WrongBranch, every end of the join is seen.
//
// @Requires MinInt < a
// @Ensures result = -a
func WrongLast(a int) (result int) {
	abs := func(n int) int {
		if n < 0 {
			return -n
		}
		return n
	}
	return abs(a) // want `vego: postcondition may not hold: result = -a`
}
