package runinv

// The callee's own writes between two runs (O1, point 2): an invariant must
// hold whatever the callee writes there.

// clobber is trusted: it may set every element of x to -1 between runs
// of f, which writes nothing of x.
func clobber(x []int, f func()) {
	for i := range x {
		x[i] = -1
		f()
	}
}

// Clobbered states of x what clobber may undo between runs.
//
// @Requires Forall i in [0, |x|) : x[i] >= 0
// @Modifies x
// @Ensures True
func Clobbered(x []int) {
	// @Invariant Forall i in [0, |x|) : x[i] >= 0 // want `invariant may not hold after clobber writes what it may write between two runs: Forall i in \[0, \|x\|\) : x\[i\] >= 0`
	clobber(x, func() {})
}

// Counted states of a variable of its own what clobber cannot touch.
//
// @Requires |x| <= 1000
// @Modifies x
// @Ensures 0 <= n <= 1000
func Counted(x []int) (n int) {
	// @Invariant 0 <= n <= 1000
	clobber(x, func() {
		if n < 1000 {
			n++
		}
	})
	return n
}

// reset writes its slice between the calls of f, which its Modifies
// lists, as a verified callee under Calls.
//
// @Calls f()
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func reset(xs []int, f func()) {
	f()
	xs[0] = -1
	f()
}

// Reset states of xs what reset writes between the runs.
//
// @Requires |xs| > 0 And xs[0] >= 0
// @Modifies xs
// @Ensures True
func Reset(xs []int) {
	// @Invariant xs[0] >= 0 // want `invariant may not hold after reset writes what it may write between two runs: xs\[0\] >= 0`
	reset(xs, func() {})
}

// Length states of xs what no write of an element changes.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func Length(xs []int) {
	m := len(xs)
	// @Invariant m = |xs|
	reset(xs, func() {})
	_ = m
}

// both calls f and g.
//
// @Calls f()
// @Calls g()
// @Ensures True
func both(f, g func()) {
	f()
	g()
	f()
}

// TwoLiterals hands two literals: what one keeps, the other must too.
//
// @Ensures True
func TwoLiterals() {
	a := 0
	// @Invariant a <= 1 // want `invariant may not be kept by the function literal run by both: a <= 1`
	both(func() { a = 0 }, func() { a = 2 })
	_ = a
}
