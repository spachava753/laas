// Package algorithms holds textbook routines that verify completely.
package algorithms

// Abs returns the absolute value of x. The least int has no negation.
//
// @ Requires x > MinInt
func Abs(x int) (y int) {
	if x < 0 {
		return -x
	}
	return x
}

//@ Ensures y >= 0 And (y = x Or y = -x)

// Max3 returns the largest of three numbers.
func Max3(a, b, c int) (m int) {
	return max(a, b, c)
}

//@ Ensures m >= a And m >= b And m >= c And (m = a Or m = b Or m = c)

// LinearSearch returns the first index holding target, or -1.
func LinearSearch(A []int, target int) (index int) {
	//@ Invariant 0 <= i <= |A| And target != A[0:i)
	//@ Variant |A| - i
	for i := 0; i < len(A); i++ {
		if A[i] == target {
			return i
		}
	}
	return -1
}

//@ Ensures index = -1 Or (0 <= index < |A| And A[index] = target)
//@ Ensures index = -1 -> target != A[0:|A|)
//@ Ensures index >= 0 -> target != A[0:index)

//@ Predicate sorted(A) ::= Forall i in [0, |A|) : Forall j in [i, |A|) : A[i] <= A[j]

// BinarySearch reports where target occurs in a sorted slice.
//
// @ Requires sorted(A)
func BinarySearch(A []int, target int) (index int, found bool) {
	lo, hi := 0, len(A)
	//@ Invariant 0 <= lo <= hi <= |A|
	//@ Invariant A[0:lo) < target And target < A[hi:|A|)
	//@ Variant hi - lo
	for lo < hi {
		mid := lo + (hi-lo)/2
		if A[mid] == target {
			return mid, true
		}
		if A[mid] < target {
			lo = mid + 1
		} else {
			hi = mid
		}
	}
	return -1, false
}

//@ Ensures found = True -> (0 <= index < |A| And A[index] = target)
//@ Ensures found = False -> target != A[0:|A|)

// MaxIndex returns the position of a largest element.
//
// @ Requires |A| > 0
func MaxIndex(A []int) (best int) {
	//@ Invariant 0 <= best < i <= |A| And A[0:i) <= A[best]
	//@ Variant |A| - i
	for i := 1; i < len(A); i++ {
		if A[i] > A[best] {
			best = i
		}
	}
	return best
}

//@ Ensures 0 <= best < |A| And A[0:|A|) <= A[best]

// Fill overwrites every element of A with value.
//
// @ Modifies A
func Fill(A []int, value int) {
	//@ Invariant A[0:i) = value
	for i := range A {
		A[i] = value
	}
}

//@ Ensures A'[0:|A|) = value

// Zeros returns a slice of n zeros built with append.
//
// @ Requires 0 <= n <= 1000000
func Zeros(n int) (R []int) {
	//@ Invariant 0 <= i <= n And |R| = i And R[0:i) = 0
	//@ Variant n - i
	for i := 0; i < n; i++ {
		R = append(R, 0)
	}
	return R
}

//@ Ensures |R| = n And R[0:n) = 0

// Copy returns a fresh copy of A.
func Copy(A []int) (R []int) {
	R = make([]int, len(A))
	//@ Invariant |R| = |A| And Forall k in [0, i) : R[k] = A[k]
	for i, x := range A {
		R[i] = x
	}
	return R
}

//@ Ensures R = A

// Swap exchanges two elements and leaves the rest alone.
//
// @ Requires 0 <= i < |A| And 0 <= j < |A|
// @ Modifies A
func Swap(A []int, i, j int) {
	A[i], A[j] = A[j], A[i]
}

//@ Ensures A'[i] = A[j] And A'[j] = A[i]
//@ Ensures Forall k in [0, |A|) : (k != i And k != j) -> A'[k] = A[k]

// InsertionSort sorts A in place.
//
// @ Modifies A
func InsertionSort(A []int) {
	//@ Invariant 1 <= i
	//@ Invariant Forall a in [0, i) : Forall b in [a, i) : b < |A| -> A[a] <= A[b]
	//@ Variant |A| - i
	for i := 1; i < len(A); i++ {
		j := i
		//@ Invariant 0 <= j <= i < |A|
		//@ Invariant Forall a in [0, i] : Forall b in [a, i] : (a != j And b != j) -> A[a] <= A[b]
		//@ Invariant Forall b in (j, i] : A[j] <= A[b]
		//@ Variant j
		for j > 0 && A[j-1] > A[j] {
			Swap(A, j-1, j)
			j--
		}
	}
}

//@ Ensures sorted(A')

// GCD computes the greatest common divisor by Euclid's algorithm.
//
// @ Requires a >= 0 And b >= 0
func GCD(a, b int) (g int) {
	//@ Invariant a >= 0 And b >= 0
	//@ Variant b
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

//@ Ensures g >= 0

// CountTrue counts the set flags.
func CountTrue(flags []bool) (n int) {
	//@ Invariant 0 <= n <= i
	for i := range flags {
		if !flags[i] {
			continue
		}
		n++
	}
	return n
}

//@ Ensures 0 <= n <= |flags|

// FirstNegative finds the first negative element using break.
func FirstNegative(A []int) (index int) {
	index = -1
	//@ Invariant index = -1 And A[0:i) >= 0
	for i := range A {
		if A[i] < 0 {
			index = i
			break
		}
	}
	return index
}

//@ Ensures index = -1 Or (0 <= index < |A| And A[index] < 0)

// Mid returns the midpoint without overflowing.
//
// @ Requires 0 <= lo And lo < hi
func Mid(lo, hi int) (mid int) {
	return lo + (hi-lo)/2
}

//@ Ensures lo <= mid And mid < hi

// IsEven reports whether n is even, by mutual recursion with IsOdd.
//
// @ Requires n >= 0
// @ Measure n
func IsEven(n int) (even bool) {
	if n == 0 {
		return true
	}
	return IsOdd(n - 1)
}

//@ Ensures even = True <-> n%2 = 0

// IsOdd reports whether n is odd.
//
// @ Requires n >= 0
// @ Measure n
func IsOdd(n int) (odd bool) {
	if n == 0 {
		return false
	}
	return IsEven(n - 1)
}

//@ Ensures odd = True <-> n%2 = 1

// Sign classifies x with a switch.
func Sign(x int) (s int) {
	switch {
	case x < 0:
		return -1
	case x == 0:
		return 0
	}
	return 1
}

//@ Ensures (x < 0 -> s = -1) And (x = 0 -> s = 0) And (x > 0 -> s = 1)

const limit = 10

// Clamp bounds x by a package constant, using a tagged switch.
func Clamp(x, mode int) (y int) {
	switch mode {
	case 0, 1:
		y = min(x, limit)
	case 2:
		y = max(x, -limit)
	default:
		y = x
	}
	return y
}

//@ Ensures mode = 0 -> y <= limit
//@ Ensures mode = 2 -> y >= -limit
//@ Ensures (mode < 0 Or mode > 2) -> y = x

// Sieve marks the composite numbers below n.
//
// @ Requires 2 <= n <= 1000000
func Sieve(n int) (composite []bool) {
	composite = make([]bool, n)
	//@ Invariant 2 <= i And |composite| = n
	//@ Variant n - i
	for i := 2; i < n; i++ {
		//@ Invariant j >= 0 And |composite| = n
		//@ Variant n - j
		for j := i + i; j < n; j += i {
			composite[j] = true
		}
	}
	return composite
}

//@ Ensures |composite| = n

// Reverse returns the elements of A in opposite order.
func Reverse(A []int) (R []int) {
	n := len(A)
	R = make([]int, n)
	//@ Invariant |R| = n And Forall k in [0, i) : R[k] = A[n-1-k]
	for i := range n {
		R[i] = A[n-1-i]
	}
	return R
}

//@ Ensures |R| = |A| And Forall k in [0, |A|) : R[k] = A[|A|-1-k]

// SumOfReversed shows modular reasoning: the caller only uses the contracts.
//
// @ Requires bounded(A)
func SumOfReversed(A []int) (s int) {
	B := Reverse(A)
	C := Reverse(B)
	//@ Assert C = A
	return SumLoop(C)
}

//@ Predicate sumTo(A, i, s) ::= (i <= 0 -> s = 0) And
//@   (i > 0 -> Exists t in Z : (sumTo(A, i-1, t) And s = t + A[i-1]))

//@ Predicate bounded(A) ::= |A| <= 1000000 And
//@   Forall k in [0, |A|) : (-1000000 <= A[k] And A[k] <= 1000000)

// SumLoop adds up a slice whose elements are small enough not to overflow.
//
// @ Requires bounded(A)
func SumLoop(A []int) (s int) {
	//@ Invariant sumTo(A, i, s)
	//@ Invariant -1000000*i <= s And s <= 1000000*i
	for i := range A {
		s += A[i]
	}
	return s
}

//@ Ensures sumTo(A, |A|, s)
