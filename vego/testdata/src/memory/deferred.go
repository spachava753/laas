package memory

// Lock is held or not.
type Lock struct{ held bool }

// Acquire takes the lock.
//
// @Requires l != nil And ~l.held
// @Modifies l
// @Ensures l.held'
func (l *Lock) Acquire() {
	l.held = true
}

// Release gives the lock back.
//
// @Requires l != nil And l.held
// @Modifies l
// @Ensures ~l.held'
func (l *Lock) Release() {
	l.held = false
}

// Gauge holds a number that can be set.
type Gauge struct{ n int }

// Set stores a number.
//
// @Requires g != nil
// @Modifies g
// @Ensures g.n' = n
func (g *Gauge) Set(n int) {
	g.n = n
}

// Locked holds a lock for the length of the function and gives it back on
// every way out.
//
// @Requires l != nil And ~l.held And g != nil
// @Modifies l, g
// @Ensures ~l.held' And (x >= 0 -> g.n' = x) And (x < 0 -> g.n' = g.n)
func Locked(l *Lock, g *Gauge, x int) (result int) {
	l.Acquire()
	defer l.Release()
	if x < 0 {
		return 0
	}
	g.Set(x)
	return x
}

// LockedWrong claims the lock is still held afterwards.
//
// @Requires l != nil And ~l.held
// @Modifies l
// @Ensures l.held'
func LockedWrong(l *Lock) {
	l.Acquire()
	defer l.Release()
} // want `vego: postcondition may not hold: l\.held'`

// NeverAcquired puts off a release of a lock it does not hold.
//
// @Requires l != nil And ~l.held
// @Modifies l
func NeverAcquired(l *Lock) {
	defer l.Release() // want `vego: precondition of Release may not hold: l\.held`
}

// LastFirst puts off two calls, which run last one first.
//
// @Requires g != nil
// @Modifies g
// @Ensures g.n' = 1
func LastFirst(g *Gauge) {
	defer g.Set(1)
	defer g.Set(2)
}

// LastFirstWrong claims they run in the order written.
//
// @Requires g != nil
// @Modifies g
// @Ensures g.n' = 2
func LastFirstWrong(g *Gauge) {
	defer g.Set(1)
	defer g.Set(2)
} // want `vego: postcondition may not hold: g\.n' = 2`

// SettledEarly puts off a call whose argument is worked out at the defer
// statement, not when the call runs.
//
// @Requires g != nil
// @Modifies g
// @Ensures result = 2 And g.n' = 1
func SettledEarly(g *Gauge) (result int) {
	x := 1
	defer g.Set(x)
	x = 2
	return x
}

// SettledEarlyWrong claims the call sees the later value.
//
// @Requires g != nil
// @Modifies g
// @Ensures g.n' = 2
func SettledEarlyWrong(g *Gauge) {
	x := 1
	defer g.Set(x)
	x = 2
} // want `vego: postcondition may not hold: g\.n' = 2`

// OnOneBranch puts a call off on one branch only.
//
// @Requires g != nil
// @Modifies g
// @Ensures (set -> g.n' = 5) And (~set -> g.n' = 0)
func OnOneBranch(g *Gauge, set bool) {
	g.Set(0)
	if set {
		defer g.Set(5)
	}
}

// DeferredUnlisted puts off a call that writes what the function may not.
//
// @Requires g != nil
func DeferredUnlisted(g *Gauge) {
	defer g.Set(1) // want `vego: Set may modify g, which DeferredUnlisted may not modify; list it in a // @Modifies clause`
}

// FillsResult puts off a call that writes the result through a pointer,
// after the return statement has given the result a value.
//
// @Ensures r.Num = 1 And r.Den = 2
func FillsResult() (r Ratio) {
	defer fill(&r)
	return Ratio{Num: 9, Den: 9}
}

// FillsResultWrong claims the value of the return statement stands.
//
// @Ensures r.Num = 9
func FillsResultWrong() (r Ratio) {
	defer fill(&r)
	return Ratio{Num: 9, Den: 9} // want `vego: postcondition may not hold: r\.Num = 9`
}

// DefersInLoop puts off a call in every iteration.
//
// @Requires g != nil And 0 <= n <= 3
// @Modifies g
func DefersInLoop(g *Gauge, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		defer g.Set(i) // want `vego: cannot verify DefersInLoop: defer inside a loop is not supported: how many calls it puts off is not known`
	}
}

// DefersLiteral puts off a function literal.
//
// @Requires g != nil
// @Modifies g
func DefersLiteral(g *Gauge) {
	defer func() { g.Set(1) }() // want `vego: cannot verify DefersLiteral: only a call of a named function or method can be deferred; function literals, function values, and built-in functions are not supported here`
}

// LoopThenReturn puts a call off before a loop that may return early.
//
// @Requires l != nil And ~l.held And 0 <= n <= 10
// @Modifies l
// @Ensures ~l.held'
func LoopThenReturn(l *Lock, n int) (result int) {
	l.Acquire()
	defer l.Release()
	// @Invariant 0 <= i <= n And l.held
	// @Variant n - i
	for i := 0; i < n; i++ {
		if i == 7 {
			return i
		}
	}
	return n
}
