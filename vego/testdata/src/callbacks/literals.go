package callbacks

// The trusted helpers that the programs below hand literals to.

func eachOf(xs []int, f func(i int)) {
	for i := range xs {
		if xs[i] > 0 {
			f(i)
		}
	}
}

func search(n int, f func(i int) bool) int {
	for i := 0; i < n; i++ {
		if f(i) {
			return i
		}
	}
	return -1
}

type counter struct {
	n, m int
}

func update(c *counter, f func()) {
	c.n++
	f()
}

func both(f, g func()) {
	f()
	g()
	f()
}

// InBounds indexes a slice it captures with what each passes: the
// contract under calls says 0 <= i < n, and n is |s|.
//
// @Ensures True
func InBounds(s []int) {
	each(len(s), func(i int) {
		_ = s[i]
	})
}

// PastTheEnd indexes one further.
//
// @Ensures True
func PastTheEnd(s []int) {
	each(len(s), func(i int) {
		_ = s[i+1] // want `vego: index may be out of range, in the function literal run by each at literals.go:\d+:\d+`
	})
}

// KnowsMemory relies on what is known of the memory it captures where it
// hands the literal over.
//
// @Requires Forall k in [0, |s|) : s[k] > 0
// @Ensures True
func KnowsMemory(s []int) {
	each(len(s), func(i int) {
		// @Assert s[i] > 0
	})
}

// KnowsWhatItIsGiven relies on what the contract under calls says of the
// memory at each call.
//
// @Ensures True
func KnowsWhatItIsGiven(xs []int) {
	eachOf(xs, func(i int) {
		// @Assert xs[i] > 0
	})
}

// Found assigns a variable it captures. Afterwards the variable can hold
// anything it may be given in a run, or what it held before.
//
// @Ensures True
func Found(n int) (found bool) {
	each(n, func(i int) {
		if i == 3 {
			found = true
		}
	})
	return found
}

// StillFalse claims the variable is as it was.
//
// @Ensures True
func StillFalse(n int) {
	found := false
	each(n, func(i int) {
		found = true
	})
	// @Assert ~found // want `vego: assertion may not hold: ~found`
	_ = found
}

// Unwritten keeps what no run writes.
//
// @Requires c != nil
// @Modifies c
// @Ensures c.m' = c.m
func Unwritten(c *counter) {
	each(3, func(i int) {
		c.n = i
	})
}

// Written claims a field a run writes is as it was.
//
// @Requires c != nil
// @Modifies c
// @Ensures c.n' = c.n
func Written(c *counter) {
	each(3, func(i int) {
		c.n = i
	})
} // want `vego: postcondition may not hold: c.n' = c.n`

// Outside writes what its own Modifies does not list.
//
// @Requires c != nil
// @Ensures True
func Outside(c *counter) {
	each(3, func(i int) {
		c.n = i // want `vego: c.n is assigned, which Outside may not modify; list it in a // @Modifies clause, as c\.n, in the function literal run by each at literals.go:\d+:\d+`
	})
}

// SearchesPositive is one where the call is made on one branch of &&.
//
// @Requires Forall k in [0, |s|) : s[k] > 0
// @Ensures True
func SearchesPositive(s []int) (r bool) {
	return len(s) > 0 && search(len(s), func(i int) bool { return s[i] > 0 }) >= -1
}

// OnlyIfRun knows of the call only where it is made.
//
// @Ensures r -> |s| > 0
func OnlyIfRun(s []int) (r bool) {
	return len(s) > 0 && search(len(s), func(i int) bool { return s[i] > 0 }) >= -1
}

// ReadBeside reads a variable that the call may change in the same
// statement.
//
// @Requires 0 <= x < 1000
// @Ensures True
func ReadBeside(x int) (r int) {
	return x + search(3, func(i int) bool { // want `vego: x may be read before or after the call to search, which may change it, and Go does not fix the order`
		x = i
		return false
	})
}

// Bump writes the counter that update writes itself.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Bump(c *counter) {
	update(c, func() {
		c.m = 1 // want `vego: c.m is assigned, which update may write itself while it runs the function it is handed; a function it is handed may not write what it may write, in the function literal run by update at literals.go:\d+:\d+`
	})
}

// BumpOther writes a counter of its own.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func BumpOther(c *counter) {
	d := &counter{}
	update(c, func() {
		d.m = 1
	})
}

// UpdatesAgain hands update a literal that calls update on the same
// counter, which writes it.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func UpdatesAgain(c *counter) {
	update(c, func() {
		update(c, func() {}) // want `vego: update may modify c, which update may write itself while it runs the function it is handed`
	})
}

// Interleaved hands both two literals: one moves an index, and the other
// relies on its value at the call. Each may run after the other.
//
// @Requires |s| = 1
// @Ensures True
func Interleaved(s []int) {
	k := 0
	both(func() { k = 1 }, func() {
		_ = s[k] // want `vego: index may be negative, in the function literal run by both at literals.go:\d+:\d+` `vego: index may be out of range`
	})
}

// InLoop calls each in a loop with a literal that assigns a variable; the
// loop forgets it.
//
// @Ensures True
func InLoop(n int) {
	last := 0
	for range 3 {
		// @Assert last = 0 // want `vego: assertion may not hold: last = 0`
		each(n, func(i int) { last = i })
	}
	_ = last
}

// Recurses calls itself from what it hands over, with nothing to show
// that this ends.
//
// @Ensures True
func Recurses(n int) {
	each(n, func(i int) {
		Recurses(i) // want `recursive call needs a // @Variant annotation in the doc comment of Recurses to prove termination; the cycle: Recurses calls Recurses at literals.go:\d+:\d+, in the function literal run by each at literals.go:\d+:\d+`
	})
}

// Descends does it with a variant: each passes numbers below n.
//
// @Requires n >= 0
// @Variant n
// @Ensures True
func Descends(n int) {
	each(n, func(i int) {
		Descends(i)
	})
}

// Deferred puts the call off.
//
// @Ensures True
func Deferred() {
	defer each(2, func(i int) {}) // want `cannot verify Deferred: deferring a call of each, which calls a function it is given, is not supported yet`
}

// AsValue uses each as a value.
//
// @Ensures v != nil
func AsValue() (v Runner) {
	return each // want `cannot verify AsValue: each calls a function it is given, and cannot be used as a value`
}

// Runner is something to run.
//
// @Requires n >= 0
type Runner func(n int, f func(i int))

// Visitor is called with a position.
//
// @Requires 0 <= i
type Visitor func(i int)

// HandsOnValue makes a literal into a value that, when it runs, hands each
// a literal that calls a value.
//
// @Requires p != nil
// @Ensures v != nil
func HandsOnValue(p Visitor) (v Visitor) {
	return func(i int) {
		each(i, func(j int) {
			p(j) // want `cannot verify HandsOnValue: the function literal used as a value calls through the function value p`
		})
	}
}

// HandsPlain makes a literal into a value that hands each a literal that
// calls nothing.
//
// @Ensures v != nil
func HandsPlain() (v Visitor) {
	return func(i int) {
		each(i, func(j int) {})
	}
}

// GuardedRead relies, in what it hands over, on the left of &&.
//
// @Ensures True
func GuardedRead(s []int) (r bool) {
	return len(s) > 0 && search(1, func(i int) bool { return s[0] > 0 }) >= 0
}

// UnguardedRead does not have it.
//
// @Ensures True
func UnguardedRead(s []int) (r bool) {
	return len(s) >= 0 && search(1, func(i int) bool { return s[0] > 0 }) >= 0 // want `vego: index may be out of range, in the function literal run by search`
}
