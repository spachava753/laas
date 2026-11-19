package closures

// ReadsAround reads a variable beside a call of a literal that changes it.
// Go may read it before or after the call.
//
// @Requires 0 <= x <= 1000
// @Ensures True
func ReadsAround(x int) (result int) {
	bump := func() int {
		x = x + 1
		return 0
	}
	return x + bump() // want `vego: x may be read before or after the call to bump, which may change it, and Go does not fix the order`
}

// UpdatesAround adds to a variable the result of a literal that changes
// it.
//
// @Requires 0 <= x <= 1000
// @Ensures True
func UpdatesAround(x int) (result int) {
	bump := func() int {
		x = x + 1
		return 0
	}
	x += bump() // want `vego: x may be read before or after the call to bump, which may change it, and Go does not fix the order`
	return x
}

// IndexAround indexes a slice with a variable that the literal on the right
// changes.
//
// @Requires |A| >= 2
// @Modifies A
// @Ensures True
func IndexAround(A []int) {
	i := 0
	next := func() int {
		i = 1
		return 0
	}
	A[i] = next() // want `vego: i may be read before or after the call to next, which may change it, and Go does not fix the order`
}

// FieldAround reads a field that the literal changes.
//
// @Requires 0 <= p.a <= 1000
// @Ensures True
func FieldAround(p pair) (result int) {
	setA := func() int {
		p.a = 5
		return 1
	}
	return p.a + setA() // want `vego: p.a may be read before or after the call to setA, which may change it, and Go does not fix the order`
}

// StaleAfterCall relies on what a variable held before a literal changed
// it.
//
// @Ensures True
func StaleAfterCall() {
	n := 0
	set := func() { n = 1 }
	set()
	// @Assert n = 0 // want `vego: assertion may not hold: n = 0`
	_ = n
}

// ForgetsCaptured calls, in a loop, a literal declared before it that
// changes a variable, and relies on the value from before the loop.
//
// @Requires 0 <= k <= 1000
// @Ensures result = 5
func ForgetsCaptured(k int) (result int) {
	n := 5
	bump := func() {
		if n < 2000 {
			n++
		}
	}
	// @Invariant 0 <= i <= k
	for i := range k {
		_ = i
		bump()
	}
	return n // want `vego: postcondition may not hold: result = 5`
}

// OverflowsCaptured increments a variable of the function without a bound.
//
// @Ensures True
func OverflowsCaptured(n int) (result int) {
	inc := func() { n++ } // want `vego: addition may overflow int, in the function literal called at captureddefects.go:94:2`
	inc()
	return n
}

// SecondFieldWrong claims the first field where it reads the second.
//
// @Ensures result = 1
func SecondFieldWrong() (result int) {
	p := pair{a: 1, b: 2}
	set := func() { p.a = 1 }
	set()
	return p.b // want `vego: postcondition may not hold: result = 1`
}

// SecondFieldUpdateWrong claims the update of the first field.
//
// @Ensures result = 11
func SecondFieldUpdateWrong() (result int) {
	p := pair{a: 1, b: 2}
	set := func() { p.a = 1 }
	set()
	p.b += 10
	return p.b // want `vego: postcondition may not hold: result = 11`
}

// InnerFieldWrong claims the update of the first field of the inner
// struct.
//
// @Ensures result = 12
func InnerFieldWrong() (result int) {
	p := nested{n: 1, q: pair{a: 2, b: 3}}
	set := func() { p.n = 5 }
	set()
	p.q.b += 10
	return p.q.b // want `vego: postcondition may not hold: result = 12`
}
