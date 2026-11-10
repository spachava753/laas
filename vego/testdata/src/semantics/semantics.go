// Package semantics checks that the verifier follows Go's evaluation rules.
package semantics

// Shadow returns the parameter, not the variable that shadows it.
func Shadow(x int) (y int) {
	if x > 0 {
		x := 0
		_ = x
	}
	return x // want `vego:\ postcondition\ may\ not\ hold:\ y\ =\ 0`
}

//@ Ensures y = x
//@ Ensures y = 0

// AfterLoop leaves i at zero when n is negative.
func AfterLoop(n int) (i int) {
	//@ Invariant i >= 0
	//@ Variant n - i
	for i < n {
		i++
	}
	return i // want `vego:\ postcondition\ may\ not\ hold:\ i\ =\ n`
}

//@ Ensures i >= n
//@ Ensures i = n

// AssignmentOrder uses the old value of i as the index.
//
// @ Requires |A| > 1
// @ Modifies A
func AssignmentOrder(A []int) {
	i := 0
	i, A[i] = 1, 5
	A[i] = 6
} // want `vego:\ postcondition\ may\ not\ hold:\ A'\[1\]\ =\ 5`

//@ Ensures A'[0] = 5 And A'[1] = 6
//@ Ensures A'[1] = 5

// Increment reads each element through the range value.
//
// @ Requires Forall k in [0, |A|) : A[k] < MaxInt
// @ Modifies A
func Increment(A []int) {
	//@ Invariant Forall k in [0, i) : A[k] = old(A)[k] + 1
	//@ Invariant Forall k in [i, |A|) : A[k] = old(A)[k]
	for i, x := range A {
		A[i] = x + 1
	}
}

//@ Ensures Forall k in [0, |A|) : A'[k] = A[k] + 1

// CountPositive skips with continue, which still runs the post statement.
func CountPositive(A []int) (n int) {
	//@ Invariant 0 <= i <= |A| And 0 <= n <= i
	//@ Variant |A| - i
	for i := 0; i < len(A); i++ {
		if A[i] <= 0 {
			continue
		}
		n++
	}
	return n
}

//@ Ensures 0 <= n <= |A|

// Truncates divides the way Go does: toward zero.
//
// @ Requires a = -7
func Truncates(a int) (q, r int) {
	return a / 2, a % 2 // want `vego:\ postcondition\ may\ not\ hold:\ q\ =\ \-4`
}

//@ Ensures q = -3 And r = -1
//@ Ensures q = -4

// ShortCircuit never evaluates the index when the guard fails.
func ShortCircuit(A []int, i int) (ok bool) {
	return 0 <= i && i < len(A) && A[i] == 0
}

//@ Ensures ok = True -> A[i] = 0

// EagerOr evaluates the index although the guard may have failed.
func EagerOr(A []int, i int) (ok bool) {
	return i < len(A) || A[i] == 0 // want `vego:\ index\ may\ be\ out\ of\ range`
}

//@ Ensures True

// NamedResults returns through the named variables.
func NamedResults(a, b int) (lo, hi int) {
	lo, hi = a, b
	if lo > hi {
		lo, hi = hi, lo
	}
	return
}

//@ Ensures lo <= hi And ((lo = a And hi = b) Or (lo = b And hi = a))

// Appends grows a local slice and reads it back.
//
// @ Requires -1000 <= a <= 1000 And -1000 <= b <= 1000
func Appends(a, b int) (R []int) {
	R = append(R, a)
	R = append(R, b, a+b)
	R[0]++
	return R
}

//@ Ensures |R| = 3 And R[0] = a + 1 And R[1] = b And R[2] = a + b

// Literal builds a slice from a composite literal.
//
// @ Requires a <= 1000
func Literal(a int) (s int) {
	values := []int{a, 2, 3}
	return values[0] + values[2] // want `vego:\ postcondition\ may\ not\ hold:\ s\ =\ a\ \+\ 2`
}

//@ Ensures s = a + 3
//@ Ensures s = a + 2

// InfiniteLoop can only be left by break.
//
// @ Requires n >= 0
func InfiniteLoop(n int) (i int) {
	//@ Invariant 0 <= i <= n
	//@ Variant n - i
	for {
		if i == n {
			break
		}
		i++
	}
	return i
}

//@ Ensures i = n

// CallerSeesMutation relies on the callee's contract for the new contents.
//
// @ Requires |A| > 2 And 0 <= A[2] <= 1000
// @ Modifies A
func CallerSeesMutation(A []int) (x int) {
	before := A[2]
	setFirst(A, 9)
	return A[0] + A[2] - before
}

//@ Ensures x = 9

// @ Requires |A| > 0
// @ Modifies A
func setFirst(A []int, value int) {
	A[0] = value
}

//@ Ensures A'[0] = value And Forall k in [1, |A|) : A'[k] = A[k]

// LengthSurvivesCalls knows that no callee can change a caller's length.
//
// @ Modifies A
func LengthSurvivesCalls(A []int) (n int) {
	n = len(A)
	scramble(A)
	return len(A) - n
}

//@ Ensures n = 0

func scramble(A []int) {
	for i := range A {
		A[i] = i * 7
	}
}

// NestedBreak leaves only the inner loop.
//
// @ Requires n >= 0
func NestedBreak(n int) (count int) {
	//@ Invariant 0 <= i <= n And count = i
	//@ Variant n - i
	for i := 0; i < n; i++ {
		//@ Invariant j >= 0
		//@ Variant 10 - j
		for j := 0; j < 10; j++ {
			if j == 3 {
				break
			}
		}
		count++
	}
	return count
}

//@ Ensures count = n
