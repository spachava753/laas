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
	return x + bump() // want `vego: x may be read before or after the call to bump, which may change it, and Go does not fix the order; split the statement so that the order is the one you mean, as in x0 := x before it$`
}

// Printer returns a literal as a value of a type without a contract.
//
// @Ensures True
func Printer() (f func(x int)) {
	return func(x int) {} // want `vego: cannot verify Printer: the function literal is used as a value of type func\(x int\), which has no contract; declare a named function type with a contract and use it here`
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
// @Requires l != nil And ~l.taken And 0 <= n <= 10
// @Modifies l
// @Ensures ~l.taken'
func Rounds(l *Lock, n int) {
	// @Invariant ~l.taken
	for range n {
		func() {
			l.Acquire()
			defer l.Release()
		}()
	}
}
