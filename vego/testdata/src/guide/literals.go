package guide

// The programs of the section on function literals and of the part of the
// section on defer that is about them.

// Sorted3 compares neighbours with a literal bound to a variable.
//
// @Requires |A| = 3
// @Ensures result <-> A[0] <= A[1] And A[1] <= A[2]
func Sorted3(A []int) (result bool) {
	inOrder := func(i, j int) bool { return A[i] <= A[j] }
	return inOrder(0, 1) && inOrder(1, 2)
}

// CheckEach asserts in a literal what holds at one of its calls only.
//
// @Ensures True
func CheckEach() {
	check := func(n int) {
		// @Assert n >= 0 // want `vego: assertion may not hold: n >= 0, in the function literal called at literals.go:23:2`
	}
	check(1)
	check(-1)
}

// CountNegative counts from a literal in a variable of the function.
//
// @Ensures 0 <= result <= 2
// @Ensures a >= 0 And b >= 0 -> result = 0
func CountNegative(a, b int) (result int) {
	count := 0
	check := func(x int) {
		if x < 0 {
			count++
		}
	}
	check(a)
	check(b)
	return count
}

// ReadAndBump reads a variable beside a call of the literal that changes
// it.
//
// @Requires 0 <= x < 1000
// @Ensures True
func ReadAndBump(x int) (result int) {
	bump := func() int {
		x++
		return 0
	}
	return x + bump() // want `vego: x may be read before or after the call to bump, which may change it, and Go does not fix the order; split the statement so that the order is the one you mean`
}

// each calls f for every element. It is not verified.
func each(A []int, f func(int)) {
	for _, x := range A {
		f(x)
	}
}

// Apply hands a literal to another function.
//
// @Ensures True
func Apply(A []int) {
	each(A, func(x int) {}) // want `vego: cannot verify Apply: a function literal is supported only where it is called or deferred, or as the value that declares a new variable which is only ever called; this one is used as a value`
}

// IncAndRead changes its result in a deferred literal, after the return
// has set it.
//
// @Requires c != nil And c.n < c.limit
// @Modifies c.n
// @Ensures result = c.n'
func IncAndRead(c *Counter) (result int) {
	defer func() { result = c.n }()
	c.Inc()
	return 0
}

// Rounds takes and gives back a lock in each iteration, with the release
// deferred in a literal that each iteration calls.
//
// @Requires l != nil And ~l.held And 0 <= n <= 10
// @Modifies l
// @Ensures ~l.held'
func Rounds(l *Lock, n int) {
	// @Invariant ~l.held
	for range n {
		func() {
			l.Acquire()
			defer l.Release()
		}()
	}
}
