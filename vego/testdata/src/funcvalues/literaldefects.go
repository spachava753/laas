package funcvalues

// Big adds a captured amount that nothing bounds.
//
// @Ensures f != nil
func Big(k int) (f Mapper) {
	return func(x int) int {
		return x + k // want `vego: postcondition may not hold: 0 <= y <= 2000, in the function literal used as a Mapper at literaldefects.go:\d+:\d+` `addition may overflow int`
	}
}

// Changed captures a variable that is assigned after the literal is made,
// so the literal knows nothing of it.
//
// @Ensures f != nil
func Changed() (f Mapper) {
	k := 1
	f = func(x int) int { return x + k } // want `vego: postcondition may not hold: 0 <= y <= 2000` `addition may overflow int`
	k = 5000
	return f
}

// Redeclared captures a variable that a later := assigns again.
//
// @Ensures f != nil
func Redeclared() (f Mapper) {
	k, a := 1, 2
	f = func(x int) int { return x + k } // want `vego: postcondition may not hold: 0 <= y <= 2000` `addition may overflow int`
	k, b := 5000, 3
	_, _ = a, b
	return f
}

// Incremented captures a variable that ++ changes later.
//
// @Ensures f != nil
func Incremented() (f Mapper) {
	k := 1
	f = func(x int) int { return x + k } // want `vego: postcondition may not hold: 0 <= y <= 2000` `addition may overflow int`
	k++
	return f
}

// ChangedInLiteral captures a variable that a deferred literal changes.
//
// @Ensures f != nil
func ChangedInLiteral() (f Mapper) {
	k := 1
	defer func() { k = 5000 }()
	f = func(x int) int { return x + k } // want `vego: postcondition may not hold: 0 <= y <= 2000` `addition may overflow int`
	return f
}

// Returned captures a named result, which a return assigns: n is 0 when
// the literal is made, and 1 once the function has returned.
//
// @Ensures m != nil
func Returned() (n int, m Mapper) {
	m = func(x int) int { return 10 / (1 - n) } // want `vego: possible division by zero` `subtraction may overflow int` `postcondition may not hold`
	return 1, m
}

// Shadowed uses its own parameter, which hides the one of the function.
//
// @Requires x > 0
// @Ensures f != nil
func Shadowed(x int) (f Mapper) {
	return func(x int) int { return 100 / x } // want `vego: possible division by zero`
}

// Pair2 names its parameters in one order, and the literals below in the
// other.

// SecondNotZero divides by the second parameter, which Pair promises.
//
// @Ensures p != nil
func SecondNotZero() (p Pair) {
	return func(y, x int) int { return 100 / x }
}

// FirstNotZero divides by the first parameter, which Pair does not promise.
//
// @Ensures p != nil
func FirstNotZero() (p Pair) {
	return func(y, x int) int { return 100 / y } // want `vego: possible division by zero`
}

// Memory knows where it is made that c.Retries is 1, but the literal runs
// later, when it may be anything.
//
// @Requires c != nil
// @Modifies c.Retries
// @Ensures f != nil
func Memory(c *Config) (f Mapper) {
	c.Retries = 1
	return func(x int) int { return x / c.Retries } // want `vego: possible division by zero` `pointer may be nil|postcondition may not hold`
}

// WritesCaptured writes through a captured pointer, which the contract of
// the type does not let a value do.
//
// @Requires c != nil
// @Ensures f != nil
func WritesCaptured(c *Config) (f Mapper) {
	return func(x int) int {
		c.Retries = 0 // want `vego: pointer may be nil|c.Retries is assigned, which Mapper may not modify`
		return 0
	}
}

// Counts assigns a captured variable.
//
// @Ensures f != nil
func Counts() (f Mapper) {
	n := 0
	return func(x int) int {
		n++ // want `vego: cannot verify Counts: a function literal used as a value cannot assign n, a variable of the function around it`
		return 0
	}
}

// CallsBound uses an in-place literal of the function around it.
//
// @Ensures f != nil
func CallsBound() (f Mapper) {
	zero := func() int { return 0 }
	return func(x int) int {
		return zero() // want `vego: cannot verify CallsBound: a function literal used as a value cannot use zero, which holds a function literal of the function around it`
	}
}

// Decorates returns a literal that calls the value it wraps.
//
// @Requires g != nil
// @Ensures f != nil
func Decorates(g Mapper) (f Mapper) {
	return func(x int) int {
		return g(x) // want `vego: cannot verify Decorates: the function literal used as a value calls through the function value g, and code that a function value runs cannot do that yet`
	}
}

// HandsOn returns a literal that hands a value to a function that calls it.
//
// @Ensures f != nil
func HandsOn() (f Mapper) {
	return func(x int) int {
		Apply(nil, double) // want `vego: cannot verify HandsOn: the function literal used as a value calls Apply, which may call through a function value`
		return 0
	}
}

// CallsFire returns a literal that calls a trusted function whose body
// calls a hook. Unverified code could put the literal in the hook.
//
// @Ensures f != nil
func CallsFire() (f Plainly) {
	return func(x int) int {
		fire() // want `vego: cannot verify CallsFire: the function literal used as a value calls fire, which may call through a function value`
		return 0
	}
}

// NoContract passes a literal where the type has no contract.
//
// @Ensures True
func NoContractLit() (f Plain) {
	return func(x int) int { return x } // want `vego: cannot verify NoContractLit: the function literal is used as a value of type funcvalues.Plain, which has no contract`
}

// OldOuter names a parameter of the function around the literal with old.
//
// @Ensures f != nil
func OldOuter(k int) (f Mapper) {
	return func(x int) int {
		// @Assert old(k) = k // want `vego: in Assert annotation: old\(k\): k is not a parameter`
		return 0
	}
}

// ReturnedInner makes, inside a literal, a literal that captures a named
// result of the function, which a return of the function assigns.
//
// @Ensures p != nil
func ReturnedInner() (n int, p Picker) {
	p = func() Mapper {
		return func(x int) int { return 10 / (1 - n) } // want `vego: possible division by zero` `subtraction may overflow int` `postcondition may not hold`
	}
	return 1, p
}

// MakeDivLit makes a literal whose parameter has the name of the parameter
// of the function, which knows it is positive.
//
// @Requires x > 0
// @Ensures True
func MakeDivLit(x int) (d DivBy) {
	return func(x int) int { return 100 / x } // want `vego: possible division by zero, in the function literal used as a DivBy`
}

// Added captures a variable that += changes later.
//
// @Ensures f != nil
func Added() (f Mapper) {
	k := 1
	f = func(x int) int { return x + k } // want `vego: postcondition may not hold: 0 <= y <= 2000` `addition may overflow int`
	k += 4000
	return f
}

// Counted makes a literal in each iteration of a three-clause loop, whose
// post statement assigns the variable; the literal knows nothing of it.
//
// @Requires |out| = 3
// @Modifies out
// @Ensures True
func CountedLoop(out []Mapper) {
	// @Invariant 0 <= i <= 3
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		out[i] = func(y int) int {
			return i // want `vego: postcondition may not hold: 0 <= y <= 2000`
		}
	}
}
