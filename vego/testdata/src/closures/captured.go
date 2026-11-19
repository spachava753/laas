package closures

// A function literal may assign the variables of the function around it.
// The variable is shared: the literal changes the one the function has.

// Counts increments a variable of the function from a literal.
//
// @Ensures result = 2
func Counts() (result int) {
	n := 0
	inc := func() { n++ }
	inc()
	inc()
	return n
}

// Doubles changes a parameter from a literal. The contract speaks of the
// value the parameter had at the call.
//
// @Requires 0 <= n <= 1000
// @Ensures result = 2 * n
func Doubles(n int) (result int) {
	func() { n = n * 2 }()
	return n
}

// SetsResult assigns a named result from a literal.
//
// @Ensures result = 7
func SetsResult() (result int) {
	func() { result = 7 }()
	return result
}

// Accumulates calls, in a loop, a literal declared before it that adds to
// a variable of the function; the invariant says what the loop keeps.
//
// @Requires |A| <= 1000 And Forall k in [0, |A|) : 0 <= A[k] <= 1000
// @Ensures 0 <= result <= 1000 * |A|
func Accumulates(A []int) (result int) {
	total := 0
	add := func(x int) { total += x }
	// @Invariant 0 <= total <= 1000 * i
	for i := range A {
		add(A[i])
	}
	return total
}

// Tallies joins the two ends of a literal that counts negative numbers.
//
// @Ensures 0 <= result <= 3
// @Ensures a >= 0 And b >= 0 And c >= 0 -> result = 0
// @Ensures a < 0 -> result >= 1
func Tallies(a, b, c int) (result int) {
	bad := 0
	check := func(x int) {
		if x < 0 {
			bad++
		}
	}
	check(a)
	check(b)
	check(c)
	return bad
}

// TalliesOften joins a variable 30 times: what a join makes must not grow
// with the joins before it.
//
// @Ensures 0 <= result <= 30
func TalliesOften(a, b int) (result int) {
	bad := 0
	check := func(x int) {
		if x < 0 {
			bad++
		}
	}
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	check(a)
	check(b)
	return bad
}

// SameValue reads a variable beside a call that writes it with the value
// it has, so either order gives the same sum.
//
// @Requires 0 <= x <= 1000
// @Ensures result = x + 1
func SameValue(x int) (result int) {
	keep := func() int {
		x = x + 0
		return 1
	}
	return x + keep()
}

type pair struct{ a, b int }

// OtherField reads a field of a variable beside a call that writes another
// field of it.
//
// @Requires 0 <= p.a <= 1000
// @Ensures result = p.a + 1
func OtherField(p pair) (result int) {
	setB := func() int {
		p.b = 5
		return 1
	}
	return p.a + setB()
}

// Ordered reads a variable in one statement and calls the literal that
// changes it in the next.
//
// @Requires 0 <= x <= 1000
// @Ensures result = 2*x + 1
func Ordered(x int) (result int) {
	bump := func() int {
		x = x + 1
		return x
	}
	y := x
	return y + bump()
}

type nested struct {
	n int
	q pair
}

// SecondField reads a field other than the first of a struct that a
// literal assigns.
//
// @Ensures result = 2
func SecondField() (result int) {
	p := pair{a: 1, b: 2}
	set := func() { p.a = 1 }
	set()
	return p.b
}

// SecondFieldUpdate updates a field other than the first of such a struct.
//
// @Ensures result = 12
func SecondFieldUpdate() (result int) {
	p := pair{a: 1, b: 2}
	set := func() { p.a = 1 }
	set()
	p.b += 10
	return p.b
}

// InnerField reads and updates a field inside a field of such a struct.
//
// @Ensures result = 13
func InnerField() (result int) {
	p := nested{n: 1, q: pair{a: 2, b: 3}}
	set := func() { p.n = 5 }
	set()
	p.q.b += 10
	return p.q.b
}
