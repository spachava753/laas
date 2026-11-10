// Package paper holds the listings of the VeGo paper.
package paper

// Divide computes quotient and remainder by repeated subtraction.
//
// @ Requires n >= 0 And d > 0
func Divide(n, d int) (q, r int) {
	q, r = 0, n
	//@ Invariant n >= 0 And d > 0 And n = d*q + r And 0 <= r
	//@ Variant r
	for d <= r {
		q, r = q+1, r-d
	}
	return q, r
}

//@ Ensures n = d*q + r And 0 <= r And r < d

//@ Predicate sumTo(A, i, s) ::= ((i <= 0 -> s = 0) And
//@ (i > 0 -> Exists t in Z : (sumTo(A, i-1, t) And s = t + A[i-1])))

// SumLoop adds up a slice from left to right.
func SumLoop(A []int) (s int) {
	s = 0
	//@ Invariant 0 <= i And i <= |A| And sumTo(A, i, s)
	//@ Variant |A| - i
	for i := 0; i < len(A); i++ {
		s = s + A[i]
	}
	return s
}

//@ Ensures sumTo(A, |A|, s)

//@ Predicate sumRecPred(A, i, s) ::= ((i >= |A| -> s = 0) And
//@ (i < |A| -> Exists t in Z : (sumRecPred(A, i+1, t) And s = t + A[i])))

// SumRec adds up a slice recursively.
//
// @ Requires 0 <= i And i <= |A|
// @ Measure |A| - i
func SumRec(A []int, i int) (s int) {
	if i >= len(A) {
		return 0
	}
	t := SumRec(A, i+1)
	return t + A[i]
}

//@ Ensures sumRecPred(A, i, s)
